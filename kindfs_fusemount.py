#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Prerequisite : pip install fusepy

import sqlite3
from fuse import FUSE, Operations #FuseOSError
import argparse
import os, errno, sys, stat
import math

import functools
def logme(f):
    @functools.wraps(f)
    def wrapped(*args, **kwargs):
        print(f'________ {f.__name__} {args} {kwargs}')
        return f(*args, **kwargs)
    return wrapped

def fakecontents(xxh64be, mysize):
    return ("0x%016x, %d\n" % (xxh64be+(1<<63), mysize)).encode()

class DDBfs(Operations):
    def __init__(self, dbname, init_path='/'):
        #self.conn = sqlite3.connect(f"file:{dbname}?mode=ro", uri=True)
        self.conn = sqlite3.connect(dbname)
        cur = self.conn.cursor()
        cur.execute("create index if not exists entries_parentdir_idx on entries(parentdir)")
        self.init_path=init_path
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
        """Enable to mount a sub-part of the FS when init_path!='/'"""
        path=path1.replace("/", self.init_path, 1).rstrip('/')
        return path

    #@logme
    def readdir(self, path1, offset):
        path=self.dbpath(path1)
        cur = self.conn.cursor()
        res=['.', '..']
        res.extend([k[0] for k in cur.execute("select name from entries where parentdir=? and name!=''", (path,)).fetchall()])
        for r in res:
            yield r

    #@logme
    def open(self, path1, flags):
        path=self.dbpath(path1)
        cur = self.conn.cursor()
        rs = cur.execute("select hash from entries where path=? and type='F'", (path,)).fetchall()
        if not rs:
            print("open: error " + path)
            return -errno.ENOENT
        return 0

    #@logme
    def read(self, path1, size, offset, fh=None):
        path=self.dbpath(path1)
        #print('read %s : %d' % (path, size))
        cur = self.conn.cursor()
        rs = cur.execute("select hash,size from entries where path=? and type='F'", (path,)).fetchall()
        if not rs:
            print("read: error " + path)
            return -errno.ENOENT
        return fakecontents(rs[0][0], rs[0][1])[offset:offset+size]
        #if size>len(foob):
        #    foob += bytes('\0', encoding='utf8') * (size-len(foob))
        #return foob.ljust(size,'\0')

    #@logme
    def getattr(self, path1, fh=None):
        #self.conn.row_factory = sqlite3.Row
        if path1=='/' or path1.startswith('/.Trash'):
            st={k:1000 for k in ('st_size', 'st_mtime', 'st_uid', 'st_gid', 'st_dev', 'st_ino', 'st_nlink', 'st_atime', 'st_ctime')}
            st['st_mode'] = stat.S_IFDIR | 0o755
            return st
        path=self.dbpath(path1)
        cur = self.conn.cursor()
        rs = cur.execute("select size st_size, st_mtime, st_mode, st_uid, st_gid, st_dev, hash st_ino, st_nlink, type from entries where path=?", (path,)).fetchall()
        if not rs:
            return -errno.ENOENT
        st = {k[0]:rs[0][v_idx] for v_idx,k in enumerate(cur.description)}
        st['st_atime']=0 ; st['st_ctime']=0 ; st['st_blocks'] = 0
        if st['type']=='D':
            st["st_nlink"]=2
        elif st['type']=='S':
            st['st_size'] = 0 ; st['st_mtime'] = 0 ; st["st_dev"]=0 ; st['st_mode'] = stat.S_IFLNK | 0o755 ; st['st_uid'] = 1000 ; st['st_gid'] = 1000 ; st["st_nlink"]=1
        else:
            st['st_blocks'] = math.ceil(st['st_size']/512) # By the way, it may seem obvious to the reader but I discovered that in some situations files can have identical contents/size/filename and yet have a different size returned by "du -s" (but identical size returned with "du -sb". Another way to see it is to compare with find -type f -printf "%8b %10s\t%p\n" and see that number of blocks differ despite real size is identical). This is because the default behavior for du is to rely on st_block, which may differ between identical files if the underlying filesystem is fragmented while du -b uses st_size i.e. the real file size
            st['st_size'] = len(fakecontents(rs[0][7],rs[0][0]))
        del st['type']
        return st

    #@logme
    def readlink(self,path1):
        path=self.dbpath(path1)
        cur = self.conn.cursor()
        rs = cur.execute("select symtarget from entries where path=? and type='S'", (path,)).fetchall()
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
    parser = argparse.ArgumentParser()
    parser.add_argument("dbfile", help="DB path")
    parser.add_argument("mountpoint", help="Mount point")
    args = parser.parse_args()
    FUSE(DDBfs(args.dbfile), args.mountpoint, nothreads=True, foreground=True)
