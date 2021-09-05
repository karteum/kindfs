#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Author: Adrien Demarez (adrien.demarez@free.fr)
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
import argparse
import shutil

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
            data = fh.read()
            notallzeros = any(data)
            digest.update(data)
        else:
            data = fh.read(CHUNKSIZE)
            notallzeros = any(data)
            digest.update(data)

            fh.seek(math.floor(filesize/2-CHUNKSIZE/2))
            data = fh.read(CHUNKSIZE)
            notallzeros = notallzeros | any(data)
            digest.update(data)

            fh.seek(filesize-CHUNKSIZE)
            data = fh.read(CHUNKSIZE)
            notallzeros = notallzeros | any(data)
            digest.update(data)
    res = digest.intdigest() if notallzeros else 0
    return res - (1<<63) # return integer rather than hexdigest because it is more efficient. "- (1<<63)" is there because SQLite3 unfortunately only supports signed 64 bits integers and doesn't support unsigned

def check_zerofile(filename):
    with open(filename,'rb') as fh:
        k = not any(fh.read())
        print(k)
        return k

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
    def __init__(self, dbname, domagic=False, rw=False):
        self.dbname=dbname
        self.conn = sqlite3.connect(dbname)
        self.conn.create_function("get_parentdir_len", 1, lambda x: 0 if os.path.dirname(x)=='/' else len(os.path.dirname(x)))
        self.cur = self.conn.cursor()
        self.processedfiles = 0
        self.processedsize = 0
        if rw==True:
            print('Looking for resume')
            tables = [k[0] for k in self.cur.execute("select name from sqlite_master where type='table'").fetchall()]
            if 'entries' in tables:
                mydirs = self.cur.execute("select path,size,hash,nsubfiles from entries where type='D'").fetchall()
                if len(mydirs)>0:
                    print("Resuming from previous scan")
                    self.dbcache_dirs = {k[0]:[k[1],k[2],k[3]] for k in mydirs}
                    self.cur.execute("delete from entries where type in ('F', 'S') and not parentdir in (select path from entries where type='D')")
                    #emptyf = self.cur.execute("select count(*),sum(size) from files").fetchall()
                    #self.processedfiles=emptyf[0][0]
                    #self.processedsize=emptyf[0][1]
                else:
                    print('No existing entries')
            elif 'dirs' in tables or 'files' in tables:
                sys.exit('Old DB schema. Migrate first !')
            else:
                print('No existing tables')
                self.createdb()
        else:
            self.conn.execute("PRAGMA temp_store = MEMORY") # "pragma query_only = ON" does not enable temp views...
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
        # TODO: add nsubfiles_tot for cumulative info on subfiles for dirs
        cur.executescript('''
            drop table if exists entries;
            create table entries(
                id integer primary key autoincrement,
                type CHAR(1) NOT NULL,
                path text UNIQUE NOT NULL,
                parentdir_len integer,
                parentdir text GENERATED ALWAYS AS (substr(path,1,parentdir_len)) VIRTUAL,
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
        parentdir_len = 0
        if init_path==None:
            init_path=dir.rstrip('/')
            print("\n==== Starting scan ====\n")
            self.cur.execute('insert or replace into dbsessions values (null, ?,?)', (int(self.timer_print), init_path))
            self.param_id=self.cur.lastrowid
        elif parentdir!='/':
            parentdir_len = len(dbpath(parentdir))
        curdir_len = len(dbpath(dir))

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
                    curdir_len,                         # parentdir_len
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
                    curdir_len,                       # parentdir_len
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
            parentdir_len,                    # parentdir_len
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

    def compute_duptable(self):
        cur = self.conn.cursor()
        print("Computing duplicates...")
        cur.executescript('''
            drop table if exists cachedups;
            create table cachedups (parentdir_len text, path text, type integer, hash integer, size integer, ndups integer, parentdir text GENERATED ALWAYS AS (substr(path,1,parentdir_len)) VIRTUAL);
            create index cachedups_path_idx on cachedups(path);
            create index cachedups_hash_idx on cachedups(hash);
            create index cachedups_size_idx on cachedups(size);

            insert into cachedups select parentdir_len,path,type,entries.hash,entries.size,ndups from entries inner join (select count(*) as ndups, hash, size from entries group by hash,size,type having count(*)>1) foo on entries.hash=foo.hash where entries.size=foo.size order by entries.size desc;
        ''')
        # select size,ndups,path,type,hash from cachedups where not parentdir in (select path from cachedups) order by size desc

    def showdups(self,basedir="",nres=None):
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        tables = [k[0] for k in self.cur.execute("select name from sqlite_master where type='table'").fetchall()]
        if not 'cachedups' in tables:
            self.compute_duptable()
        limit_nres = f'limit {int(nres)}' if nres else ''
        rs = cur.execute(f"select type,path,size,hash,ndups,parentdir from cachedups order by size desc {limit_nres}") #where not parentdir in (select path from cachedups)
        for ftype,path,size,hash,ndups,parentdir in rs:
            pdir_isdup = cur2.execute("select count(*) from cachedups where path=?", (parentdir,)).fetchall()[0][0]
            path_real = basedir+path
            if basedir!='' and basedir!=None and not os.path.exists(basedir+path):
                path_real = colored(path_real, 'red')
            elif pdir_isdup>0:
                path_real = colored(path_real, 'cyan') + colored(' [parent dir already in dups]', 'yellow')
            elif 'syncthing' in path_real or 'lost+found' in path_real:
                path_real = colored(path_real, 'cyan')

            #if not 'syncthing' in path_real and not 'lost+found' in path_real:
            print(colored(f"{ftype} 0x{hash+(1<<63):0>16x}, {ndups} * {size>>20} Mo : ", 'yellow') + path_real)
            #print(colored(f"{ftype} {hash}, {ndups} * {size>>20} Mo : ", 'yellow') + path_real)

    def compute_dupfiles(self,basedir=None,nres=None):
        # This function will probably be superseded soon (by showdups())
        if basedir==None:
            basedir=""
        limit_nres = f'limit {int(nres)}' if nres else ''
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        print("Computing duplicates...")
        rs1 = cur.execute(f'select xxh64be,size,count(*) from files group by xxh64be,size having count(*)>1 order by size desc {limit_nres}')
        print("Second phase")
        for xxh,size,ndups in rs1:
            paths = []
            rs2 = cur2.execute('select xxh64be,size,path from files where xxh64be=? and size=?', (xxh,size))
            for xxh2,size2,path in rs2:
                if basedir!='' and basedir!=None and not os.path.exists(basedir+path):
                    path_real = colored(basedir+path, 'red')
                else:
                    path_real = basedir+path
                if not 'syncthing' in path_real and not 'lost+found' in path_real:
                    paths.append(path_real)
            print(colored(f"0x{xxh+(1<<63):0>16x}, {ndups} * {size>>20} Mo :", 'yellow'))
            print('\t'+'\n\t'.join(paths))

    def compute_dupdirs(self,basedir=None,dirsorfiles="dirs", wherepathlike='/%', nres=None):
        # This function will probably be superseded soon (by showdups())
        # select (dups-1)*size/1048576 as sz, * from dirdups where not parentdir in (select path from dirdups)
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        limit_nres = f'limit {int(nres)}' if nres else ''
        print("Computing duplicates...")
        cur.executescript("""
            create temp view duphashes_dirs as select type,hash,size,count(*) ndups from entries where type='D' group by hash,size,type having count(*)>1;
            create temp view dupentries_dirs as select entries.type,parentdir,path,duphashes_dirs.hash,duphashes_dirs.size,ndups from entries inner join duphashes_dirs on duphashes_dirs.hash=entries.hash where entries.type='D';
            create temp view duphashes_filtered as select type,hash,size,ndups from dupentries_dirs where parentdir not in (select path from dupentries_dirs) group by hash,size,type
        """)
        rs = cur.execute(f"select hash,size,ndups from duphashes_filtered where type='D' order by size desc {limit_nres}")
        for xxh,size,ndups in rs:
            rs2=cur2.execute(f"select path from entries where type='D' and hash=? and size=? and not path like '/syncthing/%'", (xxh,size)).fetchall()
            paths = []
            l=0
            for k in rs2:
                if basedir!='' and basedir!=None:
                    mystr = basedir+k[0] if os.path.exists(basedir+k[0]) else colored(basedir+k[0], 'red')
                    l += 1 if os.path.exists(basedir+k[0]) else 0 # and not "syncthing" in (basedir+k[0]) 
                    paths.append(mystr)
                elif not 'lost+found' in k[0]: # and not 'syncthing' in k[0]
                    mystr=k[0]
                    l+=1
                    paths.append(mystr)
                else:
                    print(f"Not inserting {k[0]}")
            if l>1:
                print(colored(f"0x{xxh+(1<<63):0>16x}, {ndups} * {size>>20} Mo :", 'yellow'))
                print('\t'+'\n\t'.join(paths))

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

    def dumpdir(self, adir=''):
        cur = self.conn.cursor()
        for line in cur.execute("select path,xxh64be,size from dirs where path like ? order by path", (adir+'/%',)):
            (path,xxh64be,size) = line
            print("0x%016x, %d : %s" % (xxh64be+(1<<63), size, path.replace(adir,'')))

    def dbgsize(self):
        cur = self.conn.cursor()
        return cur.execute("select sum(size) from files").fetchall()[0][0]

    def isincluded(self, path_test, path_ref, otherddbfs=None, excluded="",docount=True,displaytrue=False,basedir="", checkfs=True):
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

    def migrate(self):
        tables = [k[0] for k in self.cur.execute("select name from sqlite_master where type='table'").fetchall()]
        if 'files' in tables and 'dirs' in tables and not 'entries' in tables:
            print("Migrating DB")
            self.cur.executescript('''
                drop table if exists entries;
                create table entries(
                    id integer primary key autoincrement,
                    type CHAR(1) NOT NULL,
                    path text UNIQUE NOT NULL,
                    parentdir_len integer,
                    parentdir text GENERATED ALWAYS AS (substr(path,1,parentdir_len)) VIRTUAL,
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

                insert into entries(type, path, parentdir_len, size, hash, magictype, st_mtime, st_mode, st_uid, st_gid, st_ino, st_nlink, st_dev, dbsession)
                select 'F', path, get_parentdir_len(path), size, xxh64be, magictype, st_mtime, st_mode, st_uid, st_gid, st_ino, st_nlink, st_dev, dbsession from files;

                insert into entries(type, path, parentdir_len, hash, symtarget, dbsession)
                select 'S', path, get_parentdir_len(path), xxh64be, target, dbsession from symlinks;

                insert into entries(type, path, parentdir_len, size, hash, st_mtime, st_mode, st_uid, st_gid, st_nlink, st_dev, nsubfiles, nsubdirs, dbsession)
                select 'D', path, get_parentdir_len(path), size, xxh64be, st_mtime, st_mode, st_uid, st_gid, st_nlink, st_dev, nsubfiles, nsubdirs, dbsession from dirs;

                drop table files;
                drop table symlinks;
                drop table dirs;
                create view files as select id,parentdir,name,path,size,hash as xxh64be,st_mtime, st_mode, st_uid, st_gid, st_ino, st_nlink, st_dev,dbsession,magictype from entries where type='F';
                create view dirs as select id,parentdir,name,path,size,nsubfiles,nsubdirs,hash as xxh64be,st_mtime, st_mode, st_uid, st_gid, st_nlink, st_dev,dbsession,magictype from entries where type='D';
                create view symlinks as select id,parentdir,name,path,symtarget as target,NULL as type,hash as xxh64be,dbsession,magictype from entries where type='S';
            ''')


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


############################################
# Main

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("dbfile", help="DB path")
    subparsers = parser.add_subparsers(dest="subcommand", required=True)

    parser_scan = subparsers.add_parser('scan', help="Scan directory")
    parser_scan.add_argument("path", help="path to scan")
    parser_scan.add_argument("--resetdb", "-R", help="Reset DB", action='store_true', default=False)

    parser_mount = subparsers.add_parser('mount')
    parser_mount.add_argument("mountpoint", help="Mount point")

    parser_isincluded = subparsers.add_parser('isincluded', help="Check whether all files in dirA/ are included in dirB/")
    parser_isincluded.add_argument('dirA', help="source dir")
    parser_isincluded.add_argument('dirB', help="dest dir")
    parser_isincluded.add_argument("--otherdb", "-o", help="otherdb", default=None)
    parser_isincluded.add_argument("--mountpoint", "-m", help="mountpoint for checking whether files are still present", default=None)

    parser_comparedb = subparsers.add_parser('comparedb', help="Compare two DB")
    parser_comparedb.add_argument('otherdb', help="DB to compare with")

    parser_migrate = subparsers.add_parser('migrate', help="Migrate DB schema")
    parser_migrate.add_argument('newdb', help="New DB filename with updated schema")

    parser_diff = subparsers.add_parser('diff', help="Show diffs between dirA/ and dirB/")
    parser_diff.add_argument('dirA', help="source dir")
    parser_diff.add_argument('dirB', help="dest dir")

    parser_dump=subparsers.add_parser('dump', help="dump DB")
    parser_dump.add_argument("--basedir", "-b", help="Basedir", default='')

    subparsers.add_parser('computehash', help="Compute hash")
    subparsers.add_parser('check_zerofile', help="Check whether file is made only of zeros (e.g. corrupted)")

    subparsers.add_parser('compute_duptable', help="Compute duptable")
    parser_dupdirs = subparsers.add_parser('showdups', help="show duplicates")
    parser_dupdirs.add_argument("--mountpoint", "-m", help="mountpoint for checking whether files are still present", default='')
    parser_dupdirs.add_argument("--limit", "-l", help="Max number of results", default=None)

    # Legacy
    parser_dupfiles = subparsers.add_parser('dupfiles', help="show duplicate files")
    parser_dupfiles.add_argument("--mountpoint", "-m", help="mountpoint for checking whether files are still present", default=None)
    parser_dupfiles.add_argument("--limit", "-l", help="Max number of results", default=None)
    parser_dupdirs = subparsers.add_parser('dupdirs', help="show duplicate dirs")
    parser_dupdirs.add_argument("--mountpoint", "-m", help="mountpoint for checking whether files are still present", default=None)
    parser_dupdirs.add_argument("--limit", "-l", help="Max number of results", default=None)

    args = parser.parse_args()

    if args.subcommand=='scan':
        if args.resetdb:
            os.remove(args.dbfile)
            #ddb.createdb()
            #ddb.conn.commit()
        ddb=DDB(args.dbfile, rw=True)
        try:
            ddb.dirscan(args.path)
            ddb.sync_db()
            ddb.conn.close()
        except(KeyboardInterrupt):
            ddb.sync_db()
            ddb.conn.close()
            print("\n_________________\nkeyboard interrupt !")
            #allsize = ddb.dbgsize()
            #print("\n_________________\nkeyboard interrupt, %d stored" % (allsize>>20))
    elif args.subcommand=='dump': # FIXME: change it to table "entries" instead of "dirs"
        ddb=DDB(args.dbfile)
        ddb.dumpdir(args.basedir)
    elif args.subcommand=='isincluded':
        ddb=DDB(args.dbfile)
        ddb.isincluded(args.dirA, args.dirB, args.otherdb, basedir=args.mountpoint)
    elif args.subcommand=='diff':
        ddb=DDB(args.dbfile)
        ddb.diff(args.dirA, args.dirB)
    elif args.subcommand=='mount':
        FUSE(DDBfs(args.dbfile), args.mountpoint, nothreads=True, foreground=True)
    elif args.subcommand=='dupdirs':
        ddb=DDB(args.dbfile)
        ddb.compute_dupdirs(basedir=args.mountpoint, nres=args.limit)
    elif args.subcommand=='dupfiles':
        ddb=DDB(args.dbfile)
        ddb.compute_dupfiles(basedir=args.mountpoint, nres=args.limit)
    elif args.subcommand=='comparedb':
        print(f"Files from {args.dbfile} that are not in {args.otherdb} (i.e. deleted files)")
        ddb=DDB(args.dbfile)
        ddb.isincluded('', '', otherddbfs=args.otherdb, basedir='', checkfs=False)
        print(f"\n_________\nFiles from {args.otherdb} that are not in {args.dbfile} (i.e. new files)")
        ddb=DDB(args.otherdb)
        ddb.isincluded('', '', otherddbfs=args.dbfile, basedir='', checkfs=False)
    elif args.subcommand=='migrate':
        shutil.copyfile(args.dbfile, args.newdb)
        ddb=DDB(args.newdb)
        ddb.migrate()
    elif args.subcommand=='computehash':
        filestat = os.stat(args.dbfile)
        entrysize = int(filestat.st_size)
        fxxh = xxhash_file(args.dbfile, entrysize)
        print(f"0x{fxxh+(1<<63):0>16x}, {entrysize>>20} Mo : {args.dbfile}")
    elif args.subcommand=='check_zerofile':
        check_zerofile(args.dbfile)
    elif args.subcommand=='compute_duptable':
        ddb=DDB(args.dbfile)
        ddb.compute_duptable()
    elif args.subcommand=='showdups':
        ddb=DDB(args.dbfile)
        ddb.showdups(basedir=args.mountpoint, nres=args.limit)
