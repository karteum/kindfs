/*
  This program can be distributed under the terms of the GNU GPLv2.
  Compile with gcc kindfs_fuse.c -o kindfs_fuse -lfuse3 -lsqlite3
*/

#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <assert.h>
#include <stdlib.h>
#include <unistd.h>

#include <sqlite3.h>

#define FUSE_USE_VERSION 31
#include <fuse3/fuse.h> // depending on the distribution, it may be directly #include <fuse.h>

static struct kindfs_data {
    const char *dbfile;
    const char *cwd;
    int show_help;
} options;

sqlite3 *db;

#define OPTION(t, p) { t, offsetof(struct kindfs_data, p), 1 }
static const struct fuse_opt option_spec[] = {
    OPTION("--db=%s", dbfile),
    OPTION("-h", show_help),
    OPTION("--help", show_help),
    FUSE_OPT_END
};

#define SQL_COMPILE(db, stmt, req) \
    if (!stmt) { \
        if (sqlite3_prepare_v2(db, req, -1, &stmt, NULL) != SQLITE_OK) { \
            sqlite3_close(db); \
            fprintf(stderr, "%s: could not compile SQL statement\n", __FUNCTION__); \
            exit(1); \
        } \
    } else { \
        sqlite3_reset(stmt); \
    }

static void *kindfs_init(struct fuse_conn_info *conn, struct fuse_config *cfg) {
    (void) conn; // avoid warning: unused parameter ‘conn’ [-Wunused-parameter]
    char dbpath_full[4096];
    //char tmp[4096];
    cfg->kernel_cache = 1; //cfg->auto_cache = 1;
    conn->want = FUSE_CAP_ASYNC_READ; //conn->want &= ~FUSE_CAP_ASYNC_READ;
    struct kindfs_data *data = (struct kindfs_data *)fuse_get_context()->private_data;
    printf("Init: cwd %s\n", data->cwd);
    strcpy(dbpath_full, data->cwd);
    //realpath(data->dbfile, tmp);
    //strcat(dbpath_full, tmp);
    strcat(dbpath_full, "/");
    strcat(dbpath_full, data->dbfile);
    printf("Init: Trying to open %s\n", dbpath_full);
    if(sqlite3_open(dbpath_full, &db)) {
        fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db));
        exit(1);
    } else fprintf(stderr, "Opened database successfully\n");

    return NULL;
}

static int fakecontents(int hash, int size, char *buf) {
    return sprintf(buf, "0x%016x, %d\n", hash+(1L<<63), size);
}

int startswith(char str1[], char str2[]) {
    int k=0;
    while (str1[k] && str2[k] && str1[k]==str2[k]) k++;
    if(!str2[k]) return 1;
    return 0;
}

static int kindfs_getattr(const char *path, struct stat *stbuf, struct fuse_file_info *fi)
{
    (void) fi;
    int k = 0;
    static sqlite3_stmt *stmt = NULL;
    char buf[256];
    SQL_COMPILE(db, stmt, "select size st_size, st_mtime, st_mode, st_uid, st_gid, st_dev, hash st_ino, st_nlink, type from entries where path=?");
    sqlite3_bind_text(stmt, 1, path, strlen(path), SQLITE_STATIC);
    memset(stbuf, 0, sizeof(struct stat));
    if (sqlite3_step(stmt) != SQLITE_ROW) return -ENOENT;
    stbuf->st_size = sqlite3_column_int64(stmt, 0);
    stbuf->st_mtime = sqlite3_column_int64(stmt, 1);
    stbuf->st_mode = sqlite3_column_int(stmt, 2);
    stbuf->st_uid = sqlite3_column_int(stmt, 3);
    stbuf->st_gid = sqlite3_column_int(stmt, 4);
    stbuf->st_dev = sqlite3_column_int64(stmt, 5); // FIXME: +(1<<63) ?
    stbuf->st_ino = sqlite3_column_int64(stmt, 6);
    stbuf->st_nlink = sqlite3_column_int(stmt, 7);
    const unsigned char *type = sqlite3_column_text(stmt, 8);
    if (*type=='F') {
        stbuf->st_blocks = stbuf->st_size >> 9;
        fakecontents(stbuf->st_ino, stbuf->st_size, buf);
        stbuf->st_size = strlen(buf);
    }
    else if (*type=='D') stbuf->st_size = 0;
    else if (*type=='S') {
        stbuf->st_size = stbuf->st_mtime = stbuf->st_dev = 0;
        stbuf->st_mode = S_IFLNK | 0755;
        stbuf->st_uid = stbuf->st_gid = 1000;
        stbuf->st_nlink = 1;
    }
    return 0;
    //sqlite3_finalize(stmt);
}

static int kindfs_opendir(const char *path, struct fuse_file_info *fi) {
    (void) fi;
    static sqlite3_stmt *stmt = NULL;
    SQL_COMPILE(db, stmt, "select hash from entries where path=? and type='D'");
    sqlite3_bind_text(stmt, 1, path, strlen(path), SQLITE_STATIC);
    return (sqlite3_step(stmt) == SQLITE_ROW) ? 0 : -ENOENT;
}

#define FUSE_FILL_DIR_DEFAULTS 0
static int kindfs_readdir(const char *path, void *buf, fuse_fill_dir_t filler, off_t offset, struct fuse_file_info *fi, enum fuse_readdir_flags flags) {
    (void) offset;
    (void) fi;
    (void) flags;

    int res = 0;
    static sqlite3_stmt *stmt = NULL;
    SQL_COMPILE(db, stmt, "select name from entries where parentdir=? and name!=''");

    filler(buf, ".", NULL, 0, FUSE_FILL_DIR_DEFAULTS);
    filler(buf, "..", NULL, 0, FUSE_FILL_DIR_DEFAULTS);
    sqlite3_bind_text(stmt, 1, path, strlen(path), SQLITE_STATIC);
    while (sqlite3_step(stmt) == SQLITE_ROW) {
        const unsigned char *name = sqlite3_column_text(stmt, 0);
        filler(buf, name, NULL, 0, FUSE_FILL_DIR_DEFAULTS);
    }

    return 0;
}

static int kindfs_open(const char *path, struct fuse_file_info *fi) {
    (void) fi;
    static sqlite3_stmt *stmt = NULL;
    SQL_COMPILE(db, stmt, "select hash from entries where path=? and type='F'");
    sqlite3_bind_text(stmt, 1, path, strlen(path), SQLITE_STATIC);
    return (sqlite3_step(stmt) == SQLITE_ROW) ? 0 : -ENOENT;
}

static int kindfs_read(const char *path, char *buf, size_t size, off_t offset, struct fuse_file_info *fi) {
    (void) fi;
    char contents[256] = {0};
    size_t len;
    static sqlite3_stmt *stmt = NULL;
    SQL_COMPILE(db, stmt, "select hash,size from entries where path=? and type='F'");

    sqlite3_bind_text(stmt, 1, path, strlen(path), SQLITE_STATIC);
    if (sqlite3_step(stmt) != SQLITE_ROW) return -ENOENT;
    int hash = sqlite3_column_int64(stmt, 0);
    int sizetot = sqlite3_column_int64(stmt, 1);
    fakecontents(hash, sizetot, contents);
    len = strlen(contents);

    if (offset < len) {
        if (offset + size > len) size = len - offset;
        memcpy(buf, contents + offset, size);
    } else size = 0;

    return size;
}

static int kindfs_readlink(const char *path, char *link, size_t size) {
    static sqlite3_stmt *stmt = NULL;
    SQL_COMPILE(db, stmt, "select symtarget from entries where path=? and type='S'");
    sqlite3_bind_text(stmt, 1, path, strlen(path), SQLITE_STATIC);
    if (sqlite3_step(stmt) != SQLITE_ROW) return -ENOENT;
    const unsigned char *symtarget = sqlite3_column_text(stmt, 0);
    strncpy(link, symtarget, size);
    return 0;
}

static const struct fuse_operations kindfs_oper = {
    .init = kindfs_init,
    .getattr = kindfs_getattr,
    .readdir = kindfs_readdir,
    .opendir = kindfs_opendir,
    .open = kindfs_open,
    .read = kindfs_read,
    .readlink = kindfs_readlink,
};

static void show_help(const char *progname) {
    printf("usage: %s [options] <mountpoint>\n\n", progname);
    printf("File-system specific options:\n"
           "    --db=<s>            path to the database\n"
           "\n");
}

int main(int argc, char *argv[]) {
    int ret;
    struct fuse_args args = FUSE_ARGS_INIT(argc, argv);
    options.dbfile = strdup("foo.db"); // FIXME: make it mandatory to specify dbfile on the CLI
    options.cwd = getcwd(NULL, 0);
    if (fuse_opt_parse(&args, &options, option_spec, NULL) == -1)
        return 1;
    /* When --help is specified, first print our own file-system specific help text, then signal fuse_main to show
       additional help (by adding `--help` to the options again) without usage: line (by setting argv[0] to the empty string) */
    if (options.show_help) {
        show_help(argv[0]);
        assert(fuse_opt_add_arg(&args, "--help") == 0);
        args.argv[0][0] = '\0';
    }
    ret = fuse_main(args.argc, args.argv, &kindfs_oper, &options);
    fuse_opt_free_args(&args);
    sqlite3_close(db);
    return ret;
}
