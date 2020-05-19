#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Feb 29 12:13:23 2020

@author: adrien
"""

import sqlite3,xxhash
import fnmatch
import math
import os, errno, sys, stat
import array
import numpy as np
from collections import defaultdict
import time
from fuse import FUSE, Operations #FuseOSError
import magic
import re

#import bisect
#import chardet
#import codecs
#import cProfile

import functools
def logme(f):
    @functools.wraps(f)
    def wrapped(*args, **kwargs):
        print('________ ' + f.__name__)
        return f(*args, **kwargs)
    return wrapped

def xxhash_file(filename, filesize=None, chunksize=1<<20, inclsize=False, inclname=False):
    """Return pseudo-hash of a file using xxhash64 on 3 MBytes of that file at its beginning/middle/end. Optionally include the size and filename into the pseudo-hash"""
    if filesize==None:
        filesize=int(os.stat(filename).st_size)
    if chunksize==None: # default value == 1<<20 i.e. 1 MByte chunk size
        CHUNKSIZE=filesize
    else:
        CHUNKSIZE=chunksize
    digest = xxhash.xxh64()
    if inclsize==True:
        digest.update(filesize)
    if inclname==True:
        digest.update(os.path.basename(filename))
    with open(filename,'rb') as fh:
        if(filesize<=3*CHUNKSIZE):
            digest.update(fh.read())
        else:
            digest.update(fh.read(CHUNKSIZE))
            fh.seek(math.floor(filesize/2-CHUNKSIZE/2))
            digest.update(fh.read(CHUNKSIZE))
            fh.seek(filesize-CHUNKSIZE)
            digest.update(fh.read(CHUNKSIZE))
    return digest.intdigest() - (1<<63) # return integer rather than hexdigest because it is more efficient. "- (1<<63)" is there because SQLite3 unfortunately only supports signed 64 bits integers and doesn't support unsigned


######################################################
# DB class

class DDB():
    def __init__(self, dbname, domagic=True):
        self.conn = sqlite3.connect(dbname)
        #self.init_path=init_path.rstrip('/')
        self.magictypes = {}
        self.domagic=domagic

    def createdb(self):
        cur = self.conn.cursor()
        # Create the DB. Notice that 'path' is duplicate information for 'parentdir/name' which may seem suboptimal, yet it is useful to have both for performance in various situations when using indexes (e.g. indexed full path is useful for FUSE)
        cur.executescript('''
            drop table if exists dbsessions;
            create table dbsessions(
                id integer primary key autoincrement,
                timestamp integer not null,
                init_path text
            );
            drop table if exists files;
            create table files(
                id integer primary key autoincrement,
                parentdir text,
                name text,
                path text,
                size integer,
                xxh64be integer,
                st_mtime integer, st_mode integer, st_uid integer, st_gid integer, st_ino integer, st_nlink integer, st_dev integer,
                dbsession integer not null,
                magictype integer,
                UNIQUE(parentdir,name,dbsession)
            );
            create index files_parentdir_idx on files(parentdir);
            create index files_name_idx on files(name);
            create index files_path_idx on files(path);
            create index files_size_idx on files(size);
            create index files_xxh64be_idx on files(xxh64be);

            drop table if exists dirs;
            create table dirs(
                id integer primary key autoincrement,
                parentdir text,
                name text,
                path text,
                size integer,
                nsubfiles integer,
                nsubdirs integer,
                xxh64be integer,
                st_mtime integer, st_mode integer, st_uid integer, st_gid integer, st_nlink integer, st_dev integer,
                dbsession integer not null,
                UNIQUE(parentdir,name,dbsession)
            );
            create index dirs_parentdir_idx on dirs(parentdir);
            create index dirs_name_idx on dirs(name);
            create index dirs_path_idx on dirs(path);
            create index dirs_size_idx on dirs(size);
            create index dirs_xxh64be_idx on dirs(xxh64be);

            drop table if exists magictypes;
            create table magictypes(
                id integer primary key autoincrement,
                magictype text
            );
            create index magictypes_magictype_idx on magictypes(magictype);

            drop table if exists symlinks;
            create table symlinks(
                id integer primary key autoincrement,
                parentdir text,
                name text,
                path text,
                target text,
                type integer,
                xxh64be integer,
                dbsession integer not null,
                UNIQUE(parentdir,name,dbsession)
            );
            create index symlinks_path_idx on symlinks(path);

            drop table if exists postops;
            create table postops (
                id integer primary key autoincrement,
                op text,
                parentdir text,
                path text,
                arg text
            );
            create index postops_parentdir_idx on postops(parentdir);
            create index postops_path_idx on postops(path);

            PRAGMA main.page_size=4096;
            PRAGMA main.cache_size=10000;
            PRAGMA main.locking_mode=EXCLUSIVE;
            PRAGMA main.synchronous=NORMAL;
        ''') # PRAGMA main.journal_mode=WAL;

    def magicid(self, path):
        if self.domagic==False:
            return 0
        magictype = re.sub(', BuildID\[sha1\]=[0-9a-f]*','',magic.from_file(path, mime=False))
        if magictype in self.magictypes:
            return self.magictypes[magictype]
        cur = self.conn.cursor()
        rs = cur.execute('insert into magictypes values(null,?)', (magictype,))
        magic_id = cur.lastrowid
        self.magictypes[magictype] = magic_id
        return magic_id

    def scandir(self, init_path1):
        #progress = progresswalk(init_path)
        init_path=init_path1.rstrip('/')
        processedfiles=0
        option_excludelist=[]
        dirsizes = defaultdict(int)
        dirxxh = defaultdict(int)
        global globalsize

        cur = self.conn.cursor()
        #cur2 = self.conn.cursor()
        # Read dircontents
        print("\n==== Reading DB ====\n")
        #allsize = cur.execute("select sum(files.size) from files inner join dirs on files.parentdir=(dirs.parentdir||'/'||dirs.name)").fetchall()[0][0]
        processedsize = cur.execute("select sum(files.size) from files").fetchall()[0][0]
        #if allsize != None:
        #    processedsize += allsize
        if processedsize==None:
            processedsize=0

        rs = cur.execute("select parentdir,name,xxh64be,size from dirs where xxh64be is not null")
        for k in rs:
            parentdir,name,xxh,dirsize = k
            curdir=parentdir+'/'+name
            dirxxh[curdir]=xxh
            dirsizes[curdir]=dirsize
            #if nsubdirs==0:
            #    processedsize += dirsize # FIXME: does't work if some dir has subdirs+inner files
            #     allsize4 = cur2.execute("select sum(size) from files where parentdir=?", [curdir]).fetchall()[0][0]
            #     if(dirsize != allsize4 and dirsize!=0):
            #         print("___ " + str((curdir,allsize4,dirsize)))

        if self.domagic==True:
            rs = cur.execute('select id,magictype from magictypes')
            for line in rs:
                magicid,magictype = line
                self.magictypes[magictype] = magicid

        print("\n==== Starting scan ====\n(already %d in DB)" % (processedsize>>20))
        mytime1=time.time()
        cur.execute('insert or replace into dbsessions values (null, ?,?)', (int(mytime1), init_path))
        param_id=cur.lastrowid
        for (_dir, dirs, files) in os.walk(bytes(init_path, encoding='utf-8'), topdown=False):
            try:
                dir=_dir.decode('utf-8')
            except UnicodeDecodeError:
                dir=_dir.decode('8859')
            #print("==> entering " + dir)
            #time.sleep(0.1)
            if dir in dirsizes: # and dir in dirxxh
            #    processedsize += dirsizes[dir]
                #print (dir + "already in DB -> skipping")
                continue
            #else:
                #allsize4 = cur2.execute("select sum(size) from files where parentdir=?", [dir]).fetchall()[0][0]
                #dirsizes[dir]=allsize4
                #print((dir,dirsizes[dir],allsize4))
                #print('\n\n')

            #dircontents[dir] = np.array([],dtype=np.int64)
            #progress.update(dir, dirs, files)
            for excludetest in option_excludelist:
                if fnmatch.fnmatch(dir, excludetest):
                    continue

            # Processing current dir
            dircontents = array.array('q') # Sorted array of hashes for the contents of current dir. array('q') is more space-efficient than linked list, and better than numpy in this phase as it can easily grow without destroying/recreating the array
            dirsize=0 # size of current dir including subdirs
            res=[] # dir contents to insert (all at once for performance) in the DB
            for _file in files:
                try:
                    file=_file.decode('utf-8')
                except UnicodeDecodeError:
                    file=_file.decode('8859')
                #print(chardet.detect(_file))
                if file=='.DS_Store':
                    continue
                path = dir + "/" + file
                foo = cur.execute("select size from files where path=?", (path,)).fetchall()
                if len(foo)>0:
                    print('Error: file ' + path + ' already in DB !' + str(foo[0]))
                    continue
                if not os.path.exists(path) or not os.access(path, os.R_OK) or not os.path.isfile(path):
                    # Skip broken symlinks, and cases where we do not have access rights. TODO: check whether access rights are tied to inode or path
                    #sys.stderr.write("Unable to access %s!\n" % (path,))
                    continue
                if os.path.islink(path):
                    ltarget = os.readlink(path)
                    lxxh = xxhash.xxh64(file + ' -> ' + ltarget).intdigest() - (1<<63)
                    dircontents.append(lxxh)
                    cur.execute('insert or replace into symlinks values (null,?,?,?,?,?,?,?)', (dir.replace(init_path, ''), file, path.replace(init_path, ''), ltarget, 0, lxxh, param_id))
                    continue
                filestat = os.lstat(path)
                filesize = int(filestat.st_size)
                processedsize+=filesize
                globalsize=processedsize
                processedfiles+=1
                dirsize += filesize
                xxh = xxhash_file(path, filesize)
                mymagicid=self.magicid(path)
                #bisect.insort(dircontents[dir], xxh)
                dircontents.append(xxh)
                res.append(( None, dir.replace(init_path, ''), file, path.replace(init_path, ''), filesize, xxh,
                    int(filestat.st_mtime), filestat.st_mode, filestat.st_uid, filestat.st_gid, filestat.st_ino, filestat.st_nlink, filestat.st_dev, param_id, mymagicid
                ))
                #reslen= '(' + '?,' * (len(res)-1) + '?)'
                #cur.execute('insert or replace into files values ' + reslen, res)

                #print("==> adding " + path)
                #sys.stderr.write("\033[2K\r%s\rScanning: [%d %%, %d MB, %d files] %s" % (" " * 500, 100*processedsize/totalsize/1024, processedsize>>20, processedfiles, path))
                #progress.updatef()
                mytime2=time.time()
                if (int(mytime2)%10) ==0 :
                    self.conn.commit()

                if mytime2-mytime1>0.1:
                    sys.stderr.write("\033[2K\rScanning: [%d MB, %d files] %s" % (processedsize>>20, processedfiles, dir))
                    sys.stderr.flush()
                    #conn.commit()
                    mytime1=mytime2

            for _mydir in dirs:
                try:
                    mydir=_mydir.decode('utf-8')
                except UnicodeDecodeError:
                    mydir=_mydir.decode('8859')
                mypath=dir+'/'+mydir
                if os.path.islink(mypath):
                    ltarget = os.readlink(mypath)
                    lxxh = xxhash.xxh64(mydir + ' -> ' + ltarget).intdigest() - (1<<63)
                    dircontents.append(lxxh)
                    cur.execute('insert or replace into symlinks values (null,?,?,?,?,?,?,?)', (dir.replace(init_path, ''), mydir, mypath.replace(init_path, ''), ltarget, 1, lxxh, param_id))
                    #print('dir symlink !')
                elif mypath in dirxxh and mypath in dirsizes:
                    dircontents.append(dirxxh[mypath])
                    dirsize += dirsizes[mypath]
                    #print(mypath + " OK")
                else: #if we do bottom-up, all subdirs are processed before the current dir so this should never happen
                    print("Problem : " + mypath + " not precomputed")
                    #rs = cur.execute("select xxh64be,size from dirs where parentdir='%s' and name in %s" % (dir, "('"+"','".join(dirs)+"')"))
                    #rs = cur.execute("select xxh64be,size from dirs where parentdir=? and name=?", (dir, mydir))
                    #for k in rs:
                    #    dircontents.append(k[0])
                    #    dirsize += k[1]

            # Increment all parents dir size with current dir size
            #dirtmp=dir
            #while(dirsize > 0 and dirtmp != init_path and dirtmp != '/'):
            #     dirsizes[dirtmp] += dirsize
            #     dirtmp = os.path.dirname(dirtmp)

        #for (dir, dirs, files) in os.walk(init_path, topdown=False):
            # Compute "directory hash"
            foo = np.array(dircontents, dtype=np.int64)
            foo.sort()
            dxxh = xxhash.xxh64(foo.tobytes()).intdigest() - (1<<63)
            dirxxh[dir] = dxxh
            dirsizes[dir] = dirsize
            #if (parentdir != '/'):
            #    dircontents[parentdir].append(dirxxh)
            #bisect.insort(dircontents[os.path.dirname(dir)], dirxxh)
            dirstat = os.lstat(dir)
            resdir = (
                None, os.path.dirname(dir).replace(init_path, ''), os.path.basename(dir), dir.replace(init_path, ''), dirsize, len(files), len(dirs), dxxh,
                int(dirstat.st_mtime), dirstat.st_mode, dirstat.st_uid, dirstat.st_gid, dirstat.st_nlink, dirstat.st_dev, param_id
            )
            reslen2 =  '(' + '?,' * (len(resdir)-1) + '?)'
            #conn.execute('BEGIN')
            cur.execute('insert or replace into dirs values ' + reslen2, resdir)
            if len(res)>0:
                #print(str(res[0]) + '\n_____\n')
                reslen= '(' + '?,' * (len(res[0])-1) + '?)'
                cur.executemany('insert or replace into files values ' + reslen, res)

            #     conn.rollback()
            # else:
            #     conn.commit()
        print('\nDone')

    def computedups(self):
        # select * from dirs where xxh64be in (select xxh64be from dirs group by xxh64be having count(*)>1) order by size desc
        # select (dups-1)*size/1048576 as sz, * from dirdups where not parentdir in (select path from dirdups)
        cur = self.conn.cursor()
        cur.execute('create table dirdups as select dirs.*, foo.dups from dirs inner join (select count(*) as dups, xxh64be from dirs group by xxh64be having count(*)>1) foo on dirs.xxh64be=foo.xxh64be')

    def detectsubdups(self, dir1,dir2):
        cur1 = self.conn.cursor()
        cur2 = self.conn.cursor()
        rs1 = cur1.execute("select parentdir,name,xxh64be,size from dirs where parentdir like '%s%%' order by parentdir,name" %(dir1))
        rs2 = cur2.execute("select parentdir,name,xxh64be,size from dirs where parentdir like '%s%%' order by parentdir,name" %(dir2))
        while True:
            line1=rs1.fetchone()
            line2=rs2.fetchone()
            if(line1==None or line2==None):
                if line1!=None:
                    print("Line1 still has values + %s" % (str(rs1.fetchone())))
                if line2!=None:
                    print("Line2 still has values")
                break
            (parentdir1,name1,xxh64be1,size1) = line1
            (parentdir2,name2,xxh64be2,size2) = line2
            pdir1=parentdir1.replace(dir1,'')+'/'+name1
            pdir2=parentdir2.replace(dir2,'')+'/'+name2
            foo1=("(%d, 0x%016x)" % (size1, xxh64be1+(1<<63)))
            foo2=("(%d, 0x%016x)" % (size2, xxh64be2+(1<<63)))
            if(foo1!=foo2 and pdir1==pdir2):
                print(foo1 + ' | ' + foo2 + ' -> ' + pdir1)

    def dumpdir(self, adir):
        print(len(adir))
        cur = self.conn.cursor()
        rs = cur.execute("select path,xxh64be,size from dirs where path like '%s%%' order by path" % (adir))
        for line in rs:
            (path,xxh64be,size) = line
            print("0x%016x, %d : %s" % (xxh64be+(1<<63), size, path.replace(adir,'')))

    def dbgsize(self):
        cur = self.conn.cursor()
        return cur.execute("select sum(size) from files").fetchall()[0][0]

    def isincluded(self, path_test, path_ref, excluded=""):
        """Checks whether every file under path_test/ (and subdirs) has a copy somewhere in path_ref (regardless of the directory structure in path_ref/ )"""
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        rs = cur.execute("select name,xxh64be,size,path from files where size>0 and path like ? order by path", (path_test+'/%',))
        for line in rs:
            name,xxh,size,path=line
            rs2=cur2.execute("select path from files where xxh64be=? and size=? and path like ?", (xxh, size, path_ref+'/%')).fetchall()
            if len(rs2)==0 and not excluded in path:
                print("___ %s has no equivalent" % (path))
#            else:
#                print("________ %s has %s equivalents" % (path, len(rs2)))


######################################################
# FUSE FS
class DDBfs(Operations):
    def __init__(self, dbname, init_path='/'):
        dburi="file:" + dbname + "?mode=ro"
        self.conn = sqlite3.connect(dburi, uri=True)
        self.init_path=init_path
        cur = self.conn.cursor()
        self.mkdir = {}
        rs=cur.execute("select path from postops where op='mkdir'")
        for k in rs:
            src=k
            self.mkdir[src]=''
        self.rename = {}
        rs=cur.execute("select path,arg from postops where op='rename'")
        for k in rs:
            src,dst=k
            self.rename[src]=dst
        self.unlink = {}
        rs=cur.execute("select path from postops where op='unlink'")
        for k in rs:
            src=k
            self.unlink[src]=''
        self.rmdir = {}
        rs=cur.execute("select path from postops where op='rmdir'")
        for k in rs:
            src=k
            self.rmdir[src]=''
        
    #@logme
    def readdir(self, path1, offset):
        path=path1.replace("/", self.init_path, 1).rstrip('/').replace("'","''")
        print('readdir ' + path)
        cur = self.conn.cursor()
        res=['.', '..']
        rs1 = cur.execute("select name from dirs where parentdir='%s'" % (path)).fetchall()
        for k in rs1:
            if k[0]=='':
                continue
            res.append(k[0])
        rs2 = cur.execute("select name from files where parentdir='%s'" % (path)).fetchall()
        for k in rs2:
            if k[0]=='':
                continue
            res.append(k[0])
        rs3 = cur.execute("select name from symlinks where parentdir='%s'" % (path)).fetchall()
        for k in rs3:
            if k[0]=='':
                continue
            res.append(k[0])

        for r in res:
            yield r

    #@logme
    def open(self, path1, flags):
        path=path1.replace("/", self.init_path, 1).rstrip('/').replace("'","''")
        cur = self.conn.cursor()
        rs = cur.execute("select xxh64be from files where path='%s'" % (path)).fetchall()
        if not rs:
            print("open: error " + path)
            return -errno.ENOENT
        return 0

    #@logme
    def read(self, path1, size, offset, fh=None):
        path=path1.replace("/", self.init_path, 1).rstrip('/').replace("'","''")
        #print('read %s : %d' % (path, size))
        cur = self.conn.cursor()
        rs = cur.execute("select xxh64be,size from files where path='%s'" % (path)).fetchall()
        if not rs:
            print("read: error " + path)
            return -errno.ENOENT
        foo = "0x%016x, %d\n" % (rs[0][0]+(1<<63), rs[0][1]) # %20d
        foob = bytes(foo[offset:offset+size], encoding='utf8')
        #if size>len(foob):
        #    foob += bytes('\0', encoding='utf8') * (size-len(foob))
        return foob
        #return foob.ljust(size,'\0')

    #@logme
    def getattr(self, path1, fh=None):
        path=path1.replace("/", self.init_path, 1).rstrip('/').replace("'","''")
        print('getattr %s' % (path))
        #return -errno.ENOENT
        if path1=='/' or path1.startswith('/.Trash'):
            print('getattr: ' + path)
            st={}
            for k in 'st_size', 'st_mtime', 'st_uid', 'st_gid', 'st_dev', 'st_ino', 'st_nlink', 'st_atime', 'st_ctime':
                st[k] = 1000
                st['st_mode'] = stat.S_IFDIR | 0o755
            return st
        cur = self.conn.cursor()
        rs = cur.execute("select size, st_mtime, st_mode, st_uid, st_gid, st_dev, xxh64be as st_ino, 2 as st_nlink from dirs where path='%s'" % (path)).fetchall()
        if not rs:
            rs = cur.execute("select size, st_mtime, st_mode, st_uid, st_gid, st_dev, xxh64be as st_ino, st_nlink from files where path='%s'" % (path)).fetchall() # 40 as size
        if not rs:
            rs = cur.execute("select 0 as size, 0 as st_mtime, %d as st_mode, 1000 as st_uid, 1000 as st_gid, 0 as st_dev, xxh64be as st_ino, 1 as st_nlink from symlinks where path='%s'" % (stat.S_IFLNK | 0o755, path)).fetchall()
        if not rs:
            return -errno.ENOENT

        st={}
        for v,k in enumerate(('st_size', 'st_mtime', 'st_mode', 'st_uid', 'st_gid', 'st_dev', 'st_ino', 'st_nlink')):
            st[k] = rs[0][v]
        st['st_atime']=0
        st['st_ctime']=0
        return st

    #@logme
    def readlink(self,path1):
        path=path1.replace("/", self.init_path, 1).rstrip('/').replace("'","''")
        cur = self.conn.cursor()
        rs = cur.execute("select target from symlinks where path='%s'" % (path)).fetchall()
        return rs[0][0]

    #@logme
    def unlink(self, path1):
        path=path1.replace("/", self.init_path, 1).rstrip('/').replace("'","''")
        print('unlink %s' % (path))
        cur = self.conn.cursor()
        cur.execute('insert into postops values (null,?,?,?,?)', ('unlink', os.path.dirname(path), path, null))

    #@logme
    def rename(self, old, new):
        src=old.replace("/", self.init_path, 1).rstrip('/').replace("'","''")
        dst=new.replace("/", self.init_path, 1).rstrip('/').replace("'","''")
        print('rename %s %s' % (src,dst))
        cur = self.conn.cursor()
        cur.execute('insert into postops values (null,?,?,?,?)', ('rename', os.path.dirname(src), src, dst))

    #@logme
    def mkdir(self, path1, mode):
        path=path1.replace("/", self.init_path, 1).rstrip('/').replace("'","''")
        print('mkdir %s' % (path))
        cur = self.conn.cursor()
        cur.execute('insert into postops values (null,?,?,?,?)', ('mkdir', os.path.dirname(path), path, null))

    #@logme
    def rmdir(self, path1):
        path=path1.replace("/", self.init_path, 1).rstrip('/').replace("'","''")
        print('rmdir %s' % (path))
        cur = self.conn.cursor()
        cur.execute('insert into postops values (null,?,?,?,?)', ('rmdir', os.path.dirname(path), path, null))

def usage():
    print('RESETDB <dbfile> <path> | SCAN <dbfile> <path> | FUSEFS <dbfile> <path>')

############################################
# Main

globalsize=0
if __name__ == "__main__":
    if len(sys.argv)<4:
        usage()
        exit()
    opmode=sys.argv[1]
    dbname=sys.argv[2]
    basedir=sys.argv[3]
    if opmode in ('SCAN', 'RESETDB'):
        print((dbname,basedir, len(sys.argv)))
        ddb=DDB(dbname)
        if opmode=='RESETDB':
            print ('reset DB')
            ddb.createdb()
        ddb.conn.execute('BEGIN')
        try:
            ddb.scandir(basedir)
        except(KeyboardInterrupt):
            ddb.conn.commit()
            allsize = ddb.dbgsize()
            print("\n_________________\nkeyboard interrupt, %d processed, %d stored" % (globalsize>>20, allsize>>20))
            ddb.conn.close()
        ddb.conn.commit()
        ddb.conn.close()
    elif opmode=='DUMP':
        ddb=DDB(dbname, basedir)
        ddb.dumpdir(basedir)
    elif opmode=='FUSEFS':
        FUSE(DDBfs(dbname), basedir, nothreads=True, foreground=True)
    else:
        usage()
