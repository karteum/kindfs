#!/usr/bin/env python3
# -*- coding: utf-8 -*-

######################################################
# FUSE FS

def fakecontents(xxh64be, mysize):
    return ("0x%016x, %d\n" % (xxh64be+(1<<63), mysize)).encode()

class DDBfs(Operations):
    def __init__(self, dbname, init_path='/'):
        dburi="file:" + dbname + "?mode=ro"
        self.conn = sqlite3.connect(dburi, uri=True)
        self.init_path=init_path
        cur = self.conn.cursor()
        self.mkdir = {}
        for src in cur.execute("select path from postops where op='mkdir'"):
            self.mkdir[src]=''
        self.rename = {}
        for src,dst in cur.execute("select path,arg from postops where op='rename'"):
            self.rename[src]=dst
        self.unlink = {}
        for src in cur.execute("select path from postops where op='unlink'"):
            self.unlink[src]=''
        self.rmdir = {}
        for src in cur.execute("select path from postops where op='rmdir'"):
            self.rmdir[src]=''

    def dbpath(self,path1):
        path=path1.replace("/", self.init_path, 1).rstrip('/')
        return path

    #@logme
    def readdir(self, path1, offset):
        path=self.dbpath(path1)
        cur = self.conn.cursor()
        res=['.', '..']
        rs1 = cur.execute("select name from dirs where parentdir=?", (path,)).fetchall()
        for k in rs1:
            if k[0]=='':
                continue
            res.append(k[0])
        rs2 = cur.execute("select name from files where parentdir=?", (path,)).fetchall()
        for k in rs2:
            if k[0]=='':
                continue
            res.append(k[0])
        rs3 = cur.execute("select name from symlinks where parentdir=?", (path,)).fetchall()
        for k in rs3:
            if k[0]=='':
                continue
            res.append(k[0])

        for r in res:
            yield r

    #@logme
    def open(self, path1, flags):
        path=self.dbpath(path1)
        cur = self.conn.cursor()
        rs = cur.execute("select xxh64be from files where path=?", (path,)).fetchall()
        if not rs:
            print("open: error " + path)
            return -errno.ENOENT
        return 0

    #@logme
    def read(self, path1, size, offset, fh=None):
        path=self.dbpath(path1)
        #print('read %s : %d' % (path, size))
        cur = self.conn.cursor()
        rs = cur.execute("select xxh64be,size from files where path=?", (path,)).fetchall()
        if not rs:
            print("read: error " + path)
            return -errno.ENOENT
        return fakecontents(rs[0][0], rs[0][1])[offset:offset+size]
        #if size>len(foob):
        #    foob += bytes('\0', encoding='utf8') * (size-len(foob))
        #return foob.ljust(size,'\0')

    #@logme
    def getattr(self, path1, fh=None):
        if path1=='/' or path1.startswith('/.Trash'):
            st={}
            for k in 'st_size', 'st_mtime', 'st_uid', 'st_gid', 'st_dev', 'st_ino', 'st_nlink', 'st_atime', 'st_ctime':
                st[k] = 1000
            st['st_mode'] = stat.S_IFDIR | 0o755
            return st
        path=self.dbpath(path1)
        cur = self.conn.cursor()
        rs = cur.execute("select size, st_mtime, st_mode, st_uid, st_gid, st_dev, xxh64be as st_ino, 2 as st_nlink from dirs where path=?", (path,)).fetchall()
        #print(f"getattr {path1} {path} {rs}")
        if not rs:
            rs = cur.execute("select size, st_mtime, st_mode, st_uid, st_gid, st_dev, xxh64be as st_ino, st_nlink, xxh64be from files where path=?", (path,)).fetchall() # FIXME: should I leave the real st_ino ?
        if not rs:
            rs = cur.execute("select 0 as size, 0 as st_mtime, ? as st_mode, 1000 as st_uid, 1000 as st_gid, 0 as st_dev, xxh64be as st_ino, 1 as st_nlink from symlinks where path=?", (stat.S_IFLNK | 0o755, path)).fetchall()
        if not rs:
            return -errno.ENOENT

        st={}
        for v,k in enumerate(('st_size', 'st_mtime', 'st_mode', 'st_uid', 'st_gid', 'st_dev', 'st_ino', 'st_nlink')):
            st[k] = rs[0][v]
        st['st_atime']=0
        st['st_ctime']=0
        st['st_blocks'] = math.ceil(st['st_size']/512) # By the way, it may seem obvious to the reader but I discovered that in some situations files can have identical contents/size/filename and yet have a different size returned by "du -s" (but identical size returned with "du -sb". Another way to see it is to compare with find -type f -printf "%8b %10s\t%p\n" and see that number of blocks differ despite real size is identical). This is because the default behavior for du is to rely on st_block, which may differ between identical files if the underlying filesystem is fragmented while du -b uses st_size i.e. the real file size
        if stat.S_ISREG(st['st_mode']):
            st['st_size'] = len(fakecontents(rs[0][7],rs[0][0]))
        return st

    #@logme
    def readlink(self,path1):
        path=self.dbpath(path1)
        cur = self.conn.cursor()
        rs = cur.execute("select target from symlinks where path=?", (path,)).fetchall()
        return rs[0][0]

    #@logme
    def unlink(self, path1):
        path=path1.replace("/", self.init_path, 1).rstrip('/')
        print('unlink %s' % (path))
        cur = self.conn.cursor()
        cur.execute('insert into postops values (null,?,?,?,?)', ('unlink', os.path.dirname(path), path, null))

    #@logme
    def rename(self, old, new):
        src=old.replace("/", self.init_path, 1).rstrip('/')
        dst=new.replace("/", self.init_path, 1).rstrip('/')
        print('rename %s %s' % (src,dst))
        cur = self.conn.cursor()
        cur.execute('insert into postops values (null,?,?,?,?)', ('rename', os.path.dirname(src), src, dst))

    #@logme
    def mkdir(self, path1, mode):
        path=path1.replace("/", self.init_path, 1).rstrip('/')
        print('mkdir %s' % (path))
        cur = self.conn.cursor()
        cur.execute('insert into postops values (null,?,?,?,?)', ('mkdir', os.path.dirname(path), path, null))

    #@logme
    def rmdir(self, path1):
        path=path1.replace("/", self.init_path, 1).rstrip('/')
        print('rmdir %s' % (path))
        cur = self.conn.cursor()
        cur.execute('insert into postops values (null,?,?,?,?)', ('rmdir', os.path.dirname(path), path, null))

if __name__ == "__main__":
    dbname=sys.argv[1]
    basedir=sys.argv[2]
    FUSE(DDBfs(dbname), basedir, nothreads=True, foreground=True)
