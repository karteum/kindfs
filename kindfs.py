#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Author: Adrien Demarez (adrien.demarez@free.fr)
# Version: 20210411
# License: GPLv3
# Prerequisite : pip install xxhash numpy fusepy python-magic
# Beware : this software only hashes portions of files for speed (and therefore may consider that some files/dirs are identical when they are not really). Use this program at your own risk and only when you know what you are doing ! (and double-check with filenames + if unsure, triple-check with full md5sum or diff -r !)


# Parameters
DB_COMMIT_PERIODICITY=0.1  # flush/commit DB every x seconds. Higher values implies more RAM usage but higher I/O performance
FILE_HASH_CHUNKSIZE=1<<20  # default is to hash 1MB data at begin/middle/end of files i.e. 3MB total. Smaller values means faster scan but more risk to miss differences in files. set "None" if you want to scan 100% of the contents of your files for more safety (at the expense of scanning speed)

import sqlite3,xxhash
#from crc32c import crc32
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
from termcolor import colored

try:
    from os import scandir, walk
except ImportError:
    from scandir import scandir, walk
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

def xxhash_file(filename, filesize=None, chunksize=FILE_HASH_CHUNKSIZE, inclsize=False, inclname=False):
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
    def __init__(self, dbname, domagic=False, resumedb=False):
        self.dbname=dbname
        self.conn = sqlite3.connect(dbname)
        self.cur = self.conn.cursor()
        self.processedfiles = 0
        self.processedsize = 0
        if resumedb:
            print('Looking for resume')
            tables = [k[0] for k in self.cur.execute("select name from sqlite_master where type='table'").fetchall()]
            if 'files' in tables and 'dirs' in tables:
                #emptyf = self.cur.execute("select count(*),sum(size) from files").fetchall()
                #emptyf = self.cur.execute("select id from files limit 2").fetchall()
                mydirs = self.cur.execute("select path,size,xxh64be,nsubfiles from dirs").fetchall()
                if len(mydirs)>0:
                    print("Resuming from previous scan")
                    #self.processedfiles=emptyf[0][0]
                    #self.processedsize=emptyf[0][1]
                    self.dbcache_dirs = {k[0]:[k[1],k[2],k[3]] for k in mydirs}
                    #self.cur_ref = self.conn.cursor()
                    self.cur.execute("delete from files where not parentdir in (select path from dirs)")
                else:
                    print('No existing entries')
            else:
                print('No existing tables')
                self.createdb()
        #self.init_path=init_path.rstrip('/')
        self.magictypes = {}
        self.domagic=domagic
        self.param_id = 0
        self.timer_print=time.time()
        self.timer_insert=time.time()
        self.dbcache_insert=[]
        if self.domagic==True:
            for line in self.cur.execute('select id,magictype from magictypes'):
                magicid,magictype = line
                self.magictypes[magictype] = magicid

    def createdb(self):
        print("Creating / resetting DB")
        cur = self.conn.cursor()
        # Create the DB. Notice that 'path' is duplicate information for 'parentdir/name' which may seem suboptimal, yet it is useful to have both for performance in various situations when using indexes (e.g. indexed full path is useful for FUSE)
        cur.executescript('''
            drop table if exists entries;
            create table entries(
                id integer primary key autoincrement,
                type CHAR(1) NOT NULL,
                path text UNIQUE NOT NULL,
                parentdir_len integer,
                parentdir text GENERATED ALWAYS AS (substr(path,0,parentdir_len+1)) VIRTUAL,
                name text GENERATED ALWAYS AS (substr(path,parentdir_len+2)) VIRTUAL,
                size integer,
                hash integer,
                magictype integer,
                nsubdirs integer,
                nsubfiles integer,
                symtarget text,
                st_mtime integer, st_mode integer, st_uid integer, st_gid integer, st_ino integer, st_nlink integer, st_dev integer,
                dbsession integer not null
            );
            create index entries_type_idx on entries(type);
            create index entries_parentdir_idx on entries(parentdir);
            create index entries_name_idx on entries(name);
            create index entries_path_idx on entries(path);
            create index entries_size_idx on entries(size);
            create index entries_hash_idx on entries(hash);

            drop view if exists files;
            create view files as select id,parentdir,name,path,size,hash as xxh64be,st_mtime, st_mode, st_uid, st_gid, st_ino, st_nlink, st_dev,dbsession,magictype from entries where type='F';
            drop view if exists dirs;
            create view dirs as select id,parentdir,name,path,size,nsubfiles,nsubdirs,hash as xxh64be,st_mtime, st_mode, st_uid, st_gid, st_nlink, st_dev,dbsession,magictype from entries where type='D';
            drop view if exists symlinks;
            create view symlinks as select id,parentdir,name,path,symtarget as target,NULL as type,hash as xxh64be,dbsession,magictype from entries where type='S';

            drop table if exists dbsessions;
            create table dbsessions(
                id integer primary key autoincrement,
                timestamp integer not null,
                init_path text
            );

            drop table if exists magictypes;
            create table magictypes(
                id integer primary key autoincrement,
                magicmime text,
                magictype text
            );
            create index magictypes_magictype_idx on magictypes(magictype);

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

    def magicid(self, path, dofull=True, domime=True):
        if self.domagic==False or (dofull==False and domime==False):
            return 0
        magictype = re.sub(', BuildID\[sha1\]=[0-9a-f]*','',magic.from_file(path)) if dofull else None
        magicmime = magic.from_file(path, mime=True) if domime else None
        if magictype in self.magictypes:
            return self.magictypes[magictype]
        cur = self.conn.cursor()
        rs = cur.execute('insert into magictypes values(null,?,?)', (magictype,magicmime))
        magic_id = cur.lastrowid
        self.magictypes[magictype] = magic_id
        return magic_id

    def sync_db(self):
        vec=self.dbcache_insert
        if len(vec)>0 and (isinstance(vec[0],tuple) or isinstance(vec[0],list)):
            self.cur.executemany(f'insert or replace into entries values ({",".join("?" for k in vec[0])})', vec)
            vec.clear()
        self.conn.commit()

    def insert_db(self,vec, sync=False):
        """Insert line in DB with some caching in order to perform the real insert/commit in batch (for performance) rather than one-by-one"""
        if len(vec)==0:
            return
        self.dbcache_insert.append(vec)
        mytime2=time.time()
        if sync or mytime2-self.timer_insert>DB_COMMIT_PERIODICITY:
            self.sync_db()
            self.timer_insert=mytime2
            #self.cur.execute(f'insert or replace into {table} values ({",".join("?" for k in vec)})', vec) #q = '(' + '?,' * (len(vec)-1) + '?)'

    def dirscan(self, bdir, init_path=None, parentdir=None, dirstat=None, dirlevel=0):
        """Recursively scan a dir/ (taking care of encoding issues), compute checksums and store metadata in the DB"""
        if isinstance(bdir,str):
            bdir=bytes(bdir, encoding='utf-8') # This avoids issues when walking through a filesystem with various encodings...
        def dbpath(path):
            return path.replace(init_path, '')
        def printprogress():
            mytime2=time.time()
            if mytime2-self.timer_print>DB_COMMIT_PERIODICITY:
                k=dbpath(dir_printable)
                ld=len(k) - (os.get_terminal_size()[0]-40)
                if ld>0:
                    k=colored("...",'red')+k[ld:]
                sys.stderr.write(f"\033[2K\rScanning: [{self.processedsize>>20} MB, {self.processedfiles} files] {k}")
                sys.stderr.flush()
                self.timer_print=mytime2

        #print((bdir,processed,init_path,parentdir,self.mytime))
        dir,dir_printable = mydecode_path(bdir)
        if init_path==None:
            init_path=dir.rstrip('/')
            print("\n==== Starting scan ====\n")
            self.cur.execute('insert or replace into dbsessions values (null, ?,?)', (int(self.timer_print), init_path))
            self.param_id=self.cur.lastrowid
            parentdir_in_db = '/'
        else:
            parentdir_in_db = dbpath(parentdir)

        if hasattr(self,'dbcache_dirs'): # Resume / speedup scan
            mypath=dbpath(dir_printable)
            if mypath in self.dbcache_dirs:
                mysize,myxxh,mysubfiles = self.dbcache_dirs[mypath]
                self.processedfiles+=mysubfiles
                self.processedsize+=mysize
                return mysize,myxxh
            #else: # FIXME: seems counter productive (sqlite bottleneck ?)
            #    refdb_alreadythere={k[0]:k[1] for k in self.cur_ref.execute("select path,size from files where parentdir=?", (dbpath(dir_printable),)).fetchall() }

        dirsize=0 # size of current dir including subdirs
        dircontents = array.array('q') # Array of hashes for the contents of current dir. array('q') is more space-efficient than linked list, and better than numpy in this phase as it can easily grow without destroying/recreating the array
        dir_numfiles = 0
        dir_numdirs = 0
        for entry in os.scandir(bdir):
            path,path_printable = mydecode_path(entry.path)
            name,name_printable = mydecode_path(entry.name)
            path_in_db = dbpath(path_printable)
            if not os.path.exists(path) or not os.access(path, os.R_OK):
                continue
            if entry.is_dir(follow_symlinks=False):
                entrysize,dxxh = self.dirscan(entry.path,init_path=init_path,parentdir=dir_printable,dirstat=entry.stat(follow_symlinks=False),dirlevel=dirlevel+1)
                # Insertion in DB is below at dir toplevel (and this is a recursive call)
                dircontents.append(dxxh)
                dir_numdirs+=1
            elif entry.is_symlink():
                ltarget = os.readlink(path)
                lxxh = xxhash.xxh64(name + ' -> ' + ltarget).intdigest() - (1<<63)
                dircontents.append(lxxh)
                self.insert_db((
                    None,                               # id integer primary key autoincrement
                    'S',                                # type: symlink
                    path_in_db,                         # path
                    len(os.path.dirname(path_in_db)),   # parentdir_len
                    None,                               # size
                    lxxh,                               # hash
                    None, None, None,                   # magictype, nsubdirs, nsubfiles
                    ltarget,                            # symtarget
                    None,None,None,None,None,None,None, # struct stat is not needed
                    self.param_id                       # dbsession
                ))
                entrysize=0
                #dir_numfiles += 1 # FIXME: should we do it ?
            elif entry.is_file(follow_symlinks=False): # regular file. FIXME: sort by inode (like in https://github.com/pixelb/fslint/blob/master/fslint/findup) in order to speed up scanning ?
                filestat = entry.stat(follow_symlinks=False)
                entrysize = int(filestat.st_size)
                fxxh = xxhash_file(path, entrysize)
                mymagicid=self.magicid(path)
                self.insert_db((
                    None,                             # id integer primary key autoincrement
                    'F',                              # type: file
                    path_in_db,                       # path
                    len(os.path.dirname(path_in_db)), # parentdir_len
                    entrysize,                        # size
                    fxxh,                             # hash
                    mymagicid,                        # magictype
                    None, None, None,                 # nsubdirs, nsubfiles, symtarget
                    int(filestat.st_mtime), filestat.st_mode, filestat.st_uid, filestat.st_gid, filestat.st_ino, filestat.st_nlink, filestat.st_dev,
                    self.param_id                     # dbsession
                ))
                dircontents.append(fxxh) #bisect.insort(dircontents[dir], xxh)
                self.processedfiles+=1
                self.processedsize+=entrysize
                dir_numfiles += 1
            else:
                continue # e.g. named pipes...
                #print("__error__: " + path)
                #entrysize=0
            dirsize += entrysize
            printprogress()
        npdircontents = np.array(dircontents, dtype=np.int64)
        npdircontents.sort()
        dxxh = xxhash.xxh64(npdircontents.tobytes()).intdigest() - (1<<63)
        #bisect.insort(dircontents[os.path.dirname(dir)], dirxxh)
        if dirstat==None:
            dirstat = os.lstat(dir)
        path_in_db = dbpath(dir_printable)
        self.insert_db((
            None,                             # id integer primary key autoincrement
            'D',                              # type: dir
            path_in_db,                       # path
            len(os.path.dirname(path_in_db)), # parentdir_len
            dirsize,                          # size
            dxxh,                             # hash
            None,                             # magictype
            dir_numdirs,                      # nsubdirs
            dir_numfiles,                     # nsubfiles
            None,                             # symtarget
            int(dirstat.st_mtime), dirstat.st_mode, dirstat.st_uid, dirstat.st_gid, None ,dirstat.st_nlink, dirstat.st_dev,
            self.param_id                     # dbsession
        ))
        return dirsize,dxxh

    def walkupdate(self, init_path="/mnt/raid"):
        def fspath(dbpath):
            return init_path+'/'+dbpath
        if not os.path.exists(init_path) or not os.access(init_path, os.R_OK):
            return
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        for dir in cur.execute("select path from entries where path like ? and type='D' order by path", (init_path+'/%',)):
            fsdir = fspath(dir[0])
            if not os.path.exists(fsdir) or not os.access(fsdir, os.R_OK) or not os.path.isdir(fsdir):
                print(f"Deleting {dir} from DB")
                cur2.execute("delete from entries where path like ?", (fsdir+'/%',)) # FIXME: will it affect current readings ?
        for file in cur.execute("select path from entries where path like ? and (type='F' or type='S') order by path", (init_path+'/%',)):
            fsfile = fspath(file)
            if not os.path.exists(fsfile) or not os.access(fsfile, os.R_OK): # or not os.path.isfile(fsfile):
                print(f"Deleting {file} from DB")
                cur2.execute("delete from entries where path=?", (fsfile,))

    def computedups(self,basedir="/mnt/raid",dirsorfiles="dirs", wherepathlike='/%'):
        # select (dups-1)*size/1048576 as sz, * from dirdups where not parentdir in (select path from dirdups)
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        print("Computing duplicates...")
        print("___ " + basedir + " ___")
        cur.executescript(f'''
            create temp table tmp(parentdir text, path text, xxh64be integer, size integer, dups integer);
            insert into tmp select parentdir,path,xxh64be,size,foo.dups from {dirsorfiles} inner join (select count(*) as dups, xxh64be as xxh from {dirsorfiles} group by xxh64be having count(*)>1) foo on {dirsorfiles}.xxh64be=xxh where path like '{wherepathlike}';
            create index tmp_parentdir_idx on tmp(parentdir);
            create index tmp_path_idx on tmp(path);
            create index tmp_xxh64be_idx on tmp(xxh64be);
            create index tmp_size_idx on tmp(size);
        ''')
        print("Second phase")
        rs = cur.execute('select xxh64be,size,dups from tmp where parentdir not in (select path from tmp) group by xxh64be,size order by size desc limit 100')
        for xxh,size,dups in rs:
            rs2=cur2.execute(f'select path from {dirsorfiles} where xxh64be=?', (xxh,)).fetchall()
            paths = []
            l=0
            for k in rs2:
                if basedir!='':
                    mystr = basedir+k[0] if os.path.exists(basedir+k[0]) else colored(basedir+k[0], 'red')
                    l += 1 if os.path.exists(basedir+k[0]) and not "syncthing" in (basedir+k[0]) else 0
                    paths.append(mystr)
                elif not 'syncthing' in k[0] and not 'lost+found' in k[0]:
                    mystr=k[0]
                    l+=1
                    paths.append(mystr)
            if l>1:
                print(colored("0x%016x, %d * %d Mo :" % (xxh+(1<<63), dups, size>>20), 'yellow'))
                print('\t'+'\n\t'.join(paths))
        #rs = cur.execute('select * from tmp where parentdir not in (select path from tmp) order by size desc limit 100')
        #for line in rs:
            #parentdir,path,xxh,size,dups = line
            #mystr="0x%016x, %d Mo : %s" % (xxh+(1<<63), size>>20, path)
            #if os.path.exists(basedir+path):
                #print(mystr)
            #else:
                #print (colored(mystr, 'red'))

    def walk(self,init_path=''):
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        for res in cur.execute('select path from dirs where path like ? order by path',(init_path+'/%',)):
            dir=res[0]
            dirs = [k[0] for k in cur2.execute('select name from dirs where parentdir=?',(dir,))]
            files = [k[0] for k in cur2.execute("select name from entries where parentdir=? and (type='F' or type='S')",(dir,))]
            #files.append([k[0] for k in cur2.execute('select name from symlinks where parentdir=?',(dir,))])
            yield dir,dirs,files

    def getincluded(self,basedir="/mnt/raid", init_path="/mnt/raid", wherepathlike='/%', resetdb=False):
        cur = self.conn.cursor()
        print("Computing duplicates...")
        if resetdb:
            cur.executescript(f'''
                drop table if exists tmp;
                create table tmp(parentdir text, path text, xxh64be integer, size integer, dups integer, atype integer);
                insert into tmp select parentdir,path,xxh64be,size,foo.dups,0 from dirs inner join (select count(*) as dups, xxh64be as xxh from dirs group by xxh64be having count(*)>1) foo on dirs.xxh64be=xxh where path like '{wherepathlike}';
                insert into tmp select parentdir,path,xxh64be,size,foo.dups,1 from files inner join (select count(*) as dups, xxh64be as xxh from files group by xxh64be having count(*)>1) foo on files.xxh64be=xxh where path like '{wherepathlike}';
                create index tmp_parentdir_idx on tmp(parentdir);
                create index tmp_path_idx on tmp(path);
                create index tmp_xxh64be_idx on tmp(xxh64be);
                create index tmp_size_idx on tmp(size);
            ''')
        cur.executescript('''
                drop table if exists tmp2;
                create temp table tmp2 (path text, size integer,ndupdirs integer,nsubdirs integer,ndupfiles integer, nsubfiles integer);
                create index tmp2_path_idx on tmp2(path);
                create index tmp2_size_idx on tmp2(size);
        ''')
        print("Finished first part")
        cur2 = self.conn.cursor()
        c=cur.execute('select count(*) from dirs where path like ? order by path',(basedir[len(init_path):]+'/%',)).fetchone()[0]
        k=0
        for dir,nsubdirs,nsubfiles,size in cur.execute('select path,nsubdirs,nsubfiles,size from dirs where path like ? order by path',(basedir[len(init_path):]+'/%',)):
            ndupdirs=cur2.execute('select count(*) from tmp where parentdir=? and atype=0',(dir,)).fetchone()[0]
            ndupfiles=cur2.execute('select count(*) from tmp where parentdir=? and atype=1',(dir,)).fetchone()[0]
            if ndupdirs>0.8*nsubdirs or ndupfiles>0.8*nsubfiles:
                sizedupd=0
                for line in cur2.execute('select * from tmp where atype=1 and parentdir=? or parentdir in (select path from dirs where parentdir=?)',(dir,dir)): # FIXME: does not include the size of subdirs / incorrect size
                    parentdir, path, xxh64be, asize, dups, atype = line
                    if not basedir in path:
                        sizedupd+=asize
                #print((dir,size,ndupdirs,nsubdirs,ndupfiles,nsubfiles))
                cur2.execute('insert into tmp2 values (?,?,?,?,?,?)', (dir,sizedupd>>20,ndupdirs,nsubdirs,ndupfiles,nsubfiles))
            k+=1
            sys.stderr.write("\033[2K\rScanning: [%d / %d]" % (k,c)) ; sys.stderr.flush()
        print()
        for line in cur.execute("select * from tmp2 order by size desc limit 30"):
            print(line)


    def getincluded2(self,basedir="/mnt/raid", init_path="/mnt/raid",wherepathlike='/%'):
        cur = self.conn.cursor()
        print("Computing duplicates...")
        cur.executescript(f'''
            drop table if exists tmp;
            create temp table tmp(parentdir text, path text, xxh64be integer, size integer, dups integer, atype integer);
            insert into tmp select parentdir,path,xxh64be,size,foo.dups,0 from dirs inner join (select count(*) as dups, xxh64be as xxh from dirs group by xxh64be having count(*)>1) foo on dirs.xxh64be=xxh where path like '{wherepathlike}';
            insert into tmp select parentdir,path,xxh64be,size,foo.dups,1 from files inner join (select count(*) as dups, xxh64be as xxh from files group by xxh64be having count(*)>1) foo on files.xxh64be=xxh where path like '{wherepathlike}';
            create index tmp_parentdir_idx on tmp(parentdir);
            create index tmp_path_idx on tmp(path);
            create index tmp_xxh64be_idx on tmp(xxh64be);
            create index tmp_size_idx on tmp(size);

            drop table if exists tmp2;
            create temp table tmp2(path text, size integer, atype integer);
            create index tmp2_path_idx on tmp2(path);
            create index tmp2_size_idx on tmp2(size);
        ''')
        print("Finished SQL part")
        res={}
        k=0
        for (_dir, dirs, files) in os.walk(bytes(basedir, encoding='utf-8'), topdown=False):
            dir,dir_printable = mydecode_path(_dir)
            res_cur=[0,0,0,0,0,0]
            for _file in files:
                res_cur[0] += 1
                file,file_printable = mydecode_path(_file)
                if file=='.DS_Store' or file=='._.DS_Store':
                    continue
                path = dir + "/" + file
                path_printable = dir_printable + "/" + file_printable
                alreadythere = cur.execute("select size from tmp where path=? and atype=1", (path_printable[len(init_path):],)).fetchall()
                if len(alreadythere)>0:
                    res_cur[1] += 1
                    res_cur[4] = alreadythere[0][0]
                    cur.execute('insert into tmp2 values(?,?,1)', (path_printable[len(init_path):],alreadythere[0][0]))
            for _mydir in dirs:
                res_cur[2]+=1
                mydir,mydir_printable = mydecode_path(_mydir)
                mypath=dir+'/'+mydir
                mypath_printable=dir_printable+'/'+mydir_printable
                alreadythere = cur.execute("select size from tmp where path=? and atype=0", (mypath_printable[len(init_path):],)).fetchall()
                if len(alreadythere)>0:
                    res_cur[3] += 1
                    res_cur[5] = alreadythere[0][0]
                    cur.execute('insert into tmp2 values(?,?,0)', (mypath_printable[len(init_path):],alreadythere[0][0]))
            if (res_cur[1]>0.8*res_cur[0]) or (res_cur[3]>0.8*res_cur[2]):
                res[dir]=res_cur
            k+=1
            sys.stderr.write("\033[2K\rScanning: [%d dirs] %s " % (k,dir)) ; sys.stderr.flush()
        for k,v in res.items():
            print(f'{k} : {v}')
        rs=cur.execute('select * from tmp2 order by size desc limit 30')
        for k in rs:
            print(k)
        return res

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

    def isincluded(self, path_test, path_ref, otherddbfs=None, excluded="",docount=True,displaytrue=False,basedir="/mnt/raid/adrien/Musique", checkfs=True): #basedir="/mnt/raid"
        """Checks whether every file under path_test/ (and subdirs) has a copy somewhere in path_ref (regardless of the directory structure in path_ref/ )"""
        cur = self.conn.cursor()
        if otherddbfs:
            conn2 = sqlite3.connect(otherddbfs)
            cur2 = conn2.cursor()
        else:
            cur2 = self.conn.cursor()

        mycount=cur.execute("select count(*) from (select path from files where size>0 and path like ? order by id)", (path_test+"/%",)).fetchone()[0] if docount else 1
        rs = cur.execute("select name,xxh64be,size,path from files where size>0 and path like ? order by id", (path_test+'/%',))
        k=1
        if not rs or mycount==0:
            print('No results !')
        res = []
        for line in rs:
            name,xxh,size,path=line
            if excluded!="" and excluded in path:
                continue
            if not otherddbfs and path_ref=='':
                rs2=cur2.execute("select path from files where xxh64be=? and size=? and not path like ?", (xxh, size, path_test+'/%')).fetchall()
            elif otherddbfs:
                #rs2=cur2.execute("select path from files where xxh64be=? and size=? and path like ?", (xxh, size, path_ref+'/%')).fetchall()
                rs2=cur2.execute("select path from files where xxh64be=? and size=? and path like ? limit 1", (xxh, size, path_ref+'/%')).fetchall()
            else:
                rs2=cur2.execute("select path from files where xxh64be=? and size=? and path!=? and path like ?", (xxh, size, path, path_ref+'/%')).fetchall()
                #rs2=cur2.execute("select path from files where xxh64be=? and size=? and path!=?", (xxh, size, path)).fetchall()
            if not rs2 and (checkfs==False or os.path.exists(basedir+path)):
                print(colored(f"\033[2K\r  {xxh+(1<<63):0>16x}, {size>>20} Mo : {self.dbname}:{path}",'yellow'))
                #res.append(path)
            elif basedir!='': # FIXME: else ?
                # Let's check on the filesystem in case the duplicates would have been deleted compared to what's in the DB
                l=0
                if checkfs==True and len(rs2)<=20: # FIXME: "len(rs2)>20 or" is there because of performance issues with some results that have a large number of duplicates (e.g. small system/compilation files that are identical among many projects). But this workaround is suboptimal.
                    for dup in rs2:
                        #print((path,rs2[0]))
                        if not 'lost+found' in dup[0] and os.path.exists(basedir+dup[0]):
                            l+=1
                            break
                else:
                    l=len(rs2)
                if displaytrue and l!=0:
                    print(colored(f"\033[2K\r{path} ({size>>20} Mo) has the equivalent: {rs2}",'green'))
                if l==0:
                    print(colored(f"\033[2K\rNo equivalent anymore for ({size>>20} Mo) : {path}",'red'))
                    res.append(path)
            mytime2=time.time()
            if mytime2-self.timer_print>0.05:
                sys.stderr.write(f"\033[2K\rScanning: [{k} / {mycount} entries, {int(100*k/mycount)}%] ")
                sys.stderr.flush()
                self.timer_print=mytime2
            k+=1
        if otherddbfs:
            conn2.close()
        #print('\n'.join(res))
        return res

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
        path=path1.replace("/", self.init_path, 1).rstrip('/')
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
        path=path1.replace("/", self.init_path, 1).rstrip('/')
        cur = self.conn.cursor()
        rs = cur.execute("select xxh64be from files where path=?", (path,)).fetchall()
        if not rs:
            print("open: error " + path)
            return -errno.ENOENT
        return 0

    #@logme
    def read(self, path1, size, offset, fh=None):
        path=path1.replace("/", self.init_path, 1).rstrip('/')
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
        path=path1.replace("/", self.init_path, 1).rstrip('/')
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
        path=path1.replace("/", self.init_path, 1).rstrip('/')
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
        #refdb = sys.argv[4] if len(sys.argv)==5 else None
        ddb=DDB(dbname, resumedb=True)
        if opmode=='RESETDB':
            #statvfs=os.statvfs(init_path)
            #statvfs_total = (statvfs.f_frsize*statvfs.f_blocks)>>20
            #statvfs_avail = (statvfs.f_frsize*(statvfs.f_bfree))>>20
            #statvfs_used = (statvfs.f_frsize*(statvfs.f_blocks-statvfs.f_bfree))>>20
            #cur = self.conn.cursor()
            #self.processedsize = cur.execute("select sum(files.size) from files").fetchall()[0][0]
            ddb.createdb()
            ddb.conn.commit()
        #scansubdir=sys.argv[4] if len(sys.argv)==5 else ''
        #ddb.conn.execute('BEGIN')
        try:
            ddb.dirscan(basedir)
            ddb.sync_db()
            ddb.conn.close()
        except(KeyboardInterrupt):
            ddb.sync_db()
            allsize = ddb.dbgsize()
            print("\n_________________\nkeyboard interrupt, %d processed, %d stored" % (globalsize>>20, allsize>>20))
            ddb.conn.close()

    elif opmode=='DUMP':
        ddb=DDB(dbname)
        ddb.dumpdir(basedir)
    elif opmode=='ISINCLUDED':
        ddb=DDB(dbname)
        db2=sys.argv[5] if len(sys.argv)==6 else None
        ddb.isincluded(basedir,sys.argv[4],db2)
    elif opmode=='MOUNT':
        FUSE(DDBfs(dbname), basedir, nothreads=True, foreground=True)
    elif opmode=='DUPDIRS':
        ddb=DDB(dbname)
        ddb.computedups(basedir)
    elif opmode=='DUPFILES':
        ddb=DDB(dbname)
        ddb.computedups(basedir, dirsorfiles='files')
    elif opmode=='GETINCLUDED':
        ddb=DDB(dbname)
        ddb.getincluded(basedir)
    elif opmode=='COMPAREDB':
        # FIXME: change "basedir" to better variable name
        ddb=DDB(dbname)
        print(f"Files from {dbname} that are not in {basedir} (deleted files)")
        ddb.isincluded('','',otherddbfs=basedir,basedir='',checkfs=False)
        #ddb=DDB(basedir)
        #print(f"\n_________\nFiles from {basedir} that are not in {dbname}  (new files)")
        #ddb.isincluded('','',otherddbfs=dbname,basedir='',checkfs=False)
    else:
        usage()
    print()
