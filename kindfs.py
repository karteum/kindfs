#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Author: Adrien Demarez (adrien.demarez@free.fr)
# Version: 20210411
# License: GPLv3
# Prerequisite : pip install xxhash numpy fusepy python-magic
# Beware : this software only hashes portions of files for speed (and therefore may consider that some files/dirs are identical when they are not really). Use this program at your own risk and only when you know what you are doing !

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
    CHUNKSIZE=filesize if chunksize==None else chunksize # default value == 1<<20 i.e. 1 MByte chunk size
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

def mydecode_path(pathbytes,fixparts=False):
    # In worst cases, there may be a mix of encoding in the path (e.g. beginning as utf8, and starting from some point some subdirs as iso8859, and deeper in the path again some utf8). The best way would be to use convmv to fix the issue before running this script. However in real life there may not always be a way to fix the data prior to processing, and I don't want the script to fail miserably in those cases => therefore here we return two decoded string : a first string with "surrogateescape" that can be used by os.* file methods (but cannot be printed or really used as string), and another string which cannot be used by file methods (it doesn't correspond to a valid path on the filesystem) but can be printed and manipulated (and inserted in the DB). For the latter, there are two options : either use error="replace" (default behavior), or fix every subsection of the path (slower, will convert every part nicely to utf8 for printing, but will also hide under the carpet that there is an issue that deserves to be fixed with convmv on this section of the filesystem)
    # TODO: check os.fsdecode() ?
    #print(chardet.detect(pathbytes))
    if fixparts:
        pathlist=pathbytes.split(b'/')
        path_decoded=""
        for k in pathlist:
            try:
                k2=k.decode('utf-8')
            except UnicodeDecodeError:
                k2=k.decode('8859')
            path_decoded += '/'+k2
        path_printable = path_decoded[1:]
    else:
        path_printable = pathbytes.decode('utf-8',errors="replace")
    return pathbytes.decode('utf-8',errors="surrogateescape"), path_printable

######################################################
# DB class

class DDB():
    def __init__(self, dbname, domagic=False):
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

    def magicid(self, path, domime=True):
        if self.domagic==False:
            return 0
        magictype = magic.from_file(path, mime=True) if domime==True else re.sub(', BuildID\[sha1\]=[0-9a-f]*','',magic.from_file(path))
        if magictype in self.magictypes:
            return self.magictypes[magictype]
        cur = self.conn.cursor()
        rs = cur.execute('insert into magictypes values(null,?)', (magictype,))
        magic_id = cur.lastrowid
        self.magictypes[magictype] = magic_id
        return magic_id

    def scandir(self, init_path):
        #progress = progresswalk(init_path)
        init_path=init_path.rstrip('/')
        processedfiles=0
        option_excludelist=[]
        dirsizes = defaultdict(int)
        dirxxh = defaultdict(int)
        global globalsize
        aflag=False

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

        for k in cur.execute("select parentdir,name,xxh64be,size from dirs where xxh64be is not null"):
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
            for line in cur.execute('select id,magictype from magictypes'):
                magicid,magictype = line
                self.magictypes[magictype] = magicid

        print("\n==== Starting scan ====\n(already %d in DB)" % (processedsize>>20))
        mytime1=time.time()
        cur.execute('insert or replace into dbsessions values (null, ?,?)', (int(mytime1), init_path))
        param_id=cur.lastrowid
        for (_dir, dirs, files) in os.walk(bytes(init_path, encoding='utf-8'), topdown=False):
            dir,dir_printable = mydecode_path(_dir)
            #print("==> entering " + dir)
            #time.sleep(0.2)
            if dir in dirsizes: # and dir in dirxxh
                #processedsize += dirsizes[dir]
                #print (dir + "already in DB -> skipping")
                continue
            #else:
                #dirsizes[dir] = cur2.execute("select sum(size) from files where parentdir=?", [dir]).fetchall()[0][0]

            #progress.update(dir, dirs, files)
            for excludetest in option_excludelist:
                if fnmatch.fnmatch(dir, excludetest):
                    continue

            # Processing current dir
            dircontents = array.array('q') # Sorted array of hashes for the contents of current dir. array('q') is more space-efficient than linked list, and better than numpy in this phase as it can easily grow without destroying/recreating the array
            dirsize=0 # size of current dir including subdirs
            res=[] # dir contents to insert (all at once for performance) in the DB
            for _file in files:
                file,file_printable = mydecode_path(_file)
                if file=='.DS_Store':
                    continue
                path = dir + "/" + file
                path_printable = dir_printable + "/" + file_printable
                alreadythere = cur.execute("select size from files where path=?", (path_printable,)).fetchall()
                if len(alreadythere)>0:
                    print('Error: file ' + path + ' already in DB !' + str(alreadythere[0]))
                    # FIXME: add size to dirsize and xxh to dircontents ?
                    continue
                if not os.path.exists(path) or not os.access(path, os.R_OK) or not os.path.isfile(path):
                    # Skip broken symlinks, and cases where we do not have access rights. TODO: check whether access rights are tied to inode or path
                    #sys.stderr.write("Unable to access %s!\n" % (path,))
                    continue
                if os.path.islink(path):
                    ltarget = os.readlink(path)
                    lxxh = xxhash.xxh64(file + ' -> ' + ltarget).intdigest() - (1<<63)
                    dircontents.append(lxxh)
                    cur.execute('insert or replace into symlinks values (null,?,?,?,?,?,?,?)', (dir_printable.replace(init_path, ''), file_printable, path_printable.replace(init_path, ''), ltarget, 0, lxxh, param_id))
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
                res.append(( None, dir_printable.replace(init_path, ''), file_printable, path_printable.replace(init_path, ''), filesize, xxh,
                    int(filestat.st_mtime), filestat.st_mode, filestat.st_uid, filestat.st_gid, filestat.st_ino, filestat.st_nlink, filestat.st_dev, param_id, mymagicid
                ))
                #reslen= '(' + '?,' * (len(res)-1) + '?)'
                #cur.execute('insert or replace into files values ' + reslen, res)

                #sys.stderr.write("\033[2K\r%s\rScanning: [%d %%, %d MB, %d files] %s" % (" " * 500, 100*processedsize/totalsize/1024, processedsize>>20, processedfiles, path))
                #progress.updatef()
                mytime2=time.time()
                if (int(mytime2)%10)==0:
                    if aflag==True:
                        self.conn.commit()
                    aflag=False
                else:
                    aflag=True

                if mytime2-mytime1>0.2:
                    sys.stderr.write("\033[2K\rScanning: [%d MB, %d files] %s" % (processedsize>>20, processedfiles, dir_printable.replace(init_path, '')))
                    sys.stderr.flush()
                    #conn.commit()
                    mytime1=mytime2

            for _mydir in dirs:
                mydir,mydir_printable = mydecode_path(_mydir)
                mypath=dir+'/'+mydir
                mypath_printable=dir_printable+'/'+mydir_printable
                if os.path.islink(mypath):
                    ltarget = os.readlink(mypath)
                    lxxh = xxhash.xxh64(mydir + ' -> ' + ltarget).intdigest() - (1<<63)
                    dircontents.append(lxxh)
                    cur.execute('insert or replace into symlinks values (null,?,?,?,?,?,?,?)', (dir_printable.replace(init_path, ''), mydir_printable, mypath_printable.replace(init_path, ''), ltarget, 1, lxxh, param_id))
                elif mypath in dirxxh and mypath in dirsizes:
                    dircontents.append(dirxxh[mypath])
                    dirsize += dirsizes[mypath]
                else: #if we do bottom-up, all subdirs are processed before the current dir so this should never happen
                    print("Problem : " + mypath_printable + " not precomputed")
                    # FIXME: handle access rights
                    #rs = cur.execute("select xxh64be,size from dirs where parentdir='%s' and name in %s" % (dir, "('"+"','".join(dirs)+"')"))
                    #rs = cur.execute("select xxh64be,size from dirs where parentdir=? and name=?", (dir, mydir))
                    #for k in rs:
                    #    dircontents.append(k[0])
                    #    dirsize += k[1]

            # Compute "directory hash"
            npdircontents = np.array(dircontents, dtype=np.int64)
            npdircontents.sort()
            dxxh = xxhash.xxh64(npdircontents.tobytes()).intdigest() - (1<<63)
            dirxxh[dir] = dxxh
            dirsizes[dir] = dirsize
            #bisect.insort(dircontents[os.path.dirname(dir)], dirxxh)
            dirstat = os.lstat(dir)
            resdir = (
                None, os.path.dirname(dir_printable).replace(init_path, ''), os.path.basename(dir_printable), dir_printable.replace(init_path, ''), dirsize, len(files), len(dirs), dxxh,
                int(dirstat.st_mtime), dirstat.st_mode, dirstat.st_uid, dirstat.st_gid, dirstat.st_nlink, dirstat.st_dev, param_id
            )
            reslen2 =  '(' + '?,' * (len(resdir)-1) + '?)'
            #conn.execute('BEGIN')
            cur.execute('insert or replace into dirs values ' + reslen2, resdir)
            if len(res)>0:
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
        rs1 = cur1.execute("select parentdir,name,xxh64be,size from dirs where parentdir like ? order by parentdir,name", (dir1+'%',))
        rs2 = cur2.execute("select parentdir,name,xxh64be,size from dirs where parentdir like ? order by parentdir,name", (dir2+'%',))
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
        cur = self.conn.cursor()
        for line in cur.execute("select path,xxh64be,size from dirs where path like ? order by path", (adir+'/%',)):
            (path,xxh64be,size) = line
            print("0x%016x, %d : %s" % (xxh64be+(1<<63), size, path.replace(adir,'')))

    def dbgsize(self):
        cur = self.conn.cursor()
        return cur.execute("select sum(size) from files").fetchall()[0][0]

    def isincluded(self, path_test, path_ref, otherddbfs=None, excluded=""):
        """Checks whether every file under path_test/ (and subdirs) has a copy somewhere in path_ref (regardless of the directory structure in path_ref/ )"""
        cur = self.conn.cursor()
        flag=True
        if otherddbfs:
            conn2 = sqlite3.connect(otherddbfs)
            cur2 = conn2.cursor()
        else:
            cur2 = self.conn.cursor()
        mycount=cur.execute("select count(*) from (select name,xxh64be,size,path from files where size>0 and path like ? order by size desc)", (path_test+'/%',)).fetchone()[0]
        rs = cur.execute("select name,xxh64be,size,path from files where size>0 and path like ? order by size desc", (path_test+'/%',))
        k=1
        if not rs:
            print('No results !')
        for line in rs:
            name,xxh,size,path=line
            if excluded!="" and excluded in path:
                continue
            rs2=cur2.execute("select path from files where xxh64be=? and size=? and path like ?", (xxh, size, path_ref+'/%')).fetchall()
            if len(rs2)==0:
                print(f"\033[2K\rNo equivalent for ({size>>20} Mo) : {path} ")
                flag=False
            #else:
                #print("________ %s has %s equivalents" % (path, len(rs2)))
                #sys.stdout.write('.')
            sys.stderr.write("\033[2K\rScanning: [%d / %d entries] " % (k,mycount))
            sys.stderr.flush()
            k+=1
        if otherddbfs:
            conn2.close()
        return flag

    def diff(self,dir1,dir2):
        self.isincluded(dir1,dir2)
        self.isincluded(dir2,dir1)

    def diffrec(self,dir1,dir2):
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        files = cur.execute("select name,xxh64be,size,path from files where size>0 and parentdir=? order by path", (dir1,))
        for line in files:
            name,xxh,size,path=line
            rs2=cur2.execute("select path from files where xxh64be=? and size=? and parent=?", (xxh, size, dir2)).fetchall()
            if len(rs2)==0:
                print("%s has no equivalent" % (path))

        dirs = cur.execute("select name,xxh64be,size,path from dirs where size>0 and parentdir=? order by path", (dir1,))
        for line in files:
            name,xxh,size,path=line
            rs2=cur2.execute("select path from files where xxh64be=? and size=? and parent=?", (xxh, size, dir2)).fetchall()
            if len(rs2)==0:
                print("%s has no equivalent" % (path))


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

    #@logme
    def readdir(self, path1, offset):
        path=path1.replace("/", self.init_path, 1).rstrip('/').replace("'","''")
        #print('readdir ' + path)
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
        path=path1.replace("/", self.init_path, 1).rstrip('/').replace("'","''")
        cur = self.conn.cursor()
        rs = cur.execute("select xxh64be from files where path=?", (path,)).fetchall()
        if not rs:
            print("open: error " + path)
            return -errno.ENOENT
        return 0

    #@logme
    def read(self, path1, size, offset, fh=None):
        path=path1.replace("/", self.init_path, 1).rstrip('/').replace("'","''")
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
        path=path1.replace("/", self.init_path, 1).rstrip('/').replace("'","''")
        cur = self.conn.cursor()
        rs = cur.execute("select size, st_mtime, st_mode, st_uid, st_gid, st_dev, xxh64be as st_ino, 2 as st_nlink from dirs where path=?", (path,)).fetchall()
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
        path=path1.replace("/", self.init_path, 1).rstrip('/').replace("'","''")
        cur = self.conn.cursor()
        rs = cur.execute("select target from symlinks where path=?", (path,)).fetchall()
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
            ddb.conn.commit()
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
        ddb=DDB(dbname)
        ddb.dumpdir(basedir)
    elif opmode=='ISINCLUDED':
        ddb=DDB(dbname)
        ddb.isincluded(basedir,sys.argv[4],sys.argv[5])
    elif opmode=='FUSEFS':
        FUSE(DDBfs(dbname), basedir, nothreads=True, foreground=True)
    else:
        usage()
