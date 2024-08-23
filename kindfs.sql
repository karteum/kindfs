drop table if exists files;
create table files(
    id integer primary key autoincrement,
    parentdir text,
    name text,
    size integer,
    xxh64be integer,
    st_mtime integer, st_mode integer, st_uid integer, st_gid integer, st_ino integer, st_nlink integer, st_dev integer,
    sqlite_entry_created integer
);
create index files_name_idx on files(name);
create index files_size_idx on files(size);
create index files_xxh64be_idx on files(xxh64be);
drop table if exists dirs;
create table dirs(
    id integer primary key autoincrement,
    parentdir text,
    name text,
    size integer,
    nsubfiles integer,
    nsubdirs integer,
    xxh64be integer,
    st_mtime integer, st_mode integer, st_uid integer, st_gid integer, st_dev integer,
    sqlite_entry_created integer
);
create index dirs_name_idx on dirs(name);
create index dirs_size_idx on dirs(size);
create index dirs_xxh64be_idx on dirs(xxh64be);
