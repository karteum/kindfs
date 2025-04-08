#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Author: Adrien Demarez (adrien.demarez@free.fr)
# License: GPLv3
# Prerequisite : pip install xxhash numpy python-magic termcolor
# Beware : this software only hashes portions of files for speed (and therefore may consider that some files/dirs are identical when they are not really). Use this program at your own risk and only when you know what you are doing ! (and double-check with filenames + if unsure, triple-check with full md5sum or diff -r !)

# FIXME: in some cases, it makes parentdir_len=1 and parentdir="/"

# Parameters
DB_COMMIT_PERIODICITY=0.3  # flush/commit DB every x seconds. Higher values implies more RAM usage but higher I/O performance
DISPLAY_PERIODICITY=0.05
FILE_HASH_CHUNKSIZE=1<<20  # default is to hash 1MB data at begin/middle/end of files i.e. 3MB total. Smaller values means faster scan but more risk to miss differences in files. set "None" if you want to scan 100% of the contents of your files for more safety (at the expense of scanning speed)

import sqlite3,xxhash
#import fnmatch
import math
import os, errno, sys, stat
from array import array # More lightweight than numpy
from collections import defaultdict
import time
import magic
import re
from termcolor import colored
import argparse
import shutil
import filecmp

try:
    from os import scandir, walk
except ImportError:
    from scandir import scandir, walk
#import bisect
#import chardet
#import codecs
#import cProfile

def xxhash_file(filename, filesize=None, chunksize=FILE_HASH_CHUNKSIZE, inclsize=False, inclname=False):
    """Return pseudo-hash of a file using xxhash64 on 3 MBytes of that file at its beginning/middle/end. Optionally include the size and filename into the pseudo-hash"""
    if filesize==None:
        filesize=int(os.stat(filename).st_size)
    if filesize==0:
        return 0
    CHUNKSIZE=filesize if (chunksize==None or chunksize<1) else chunksize # default value == 1<<20 i.e. 1 MByte chunk size
    digest = xxhash.xxh64()
    if inclsize==True:
        digest.update(filesize)
    if inclname==True:
        digest.update(os.path.basename(filename))
    with open(filename,'rb') as fh:
        if(filesize<=3*CHUNKSIZE):
            data = fh.read() # FIXME: what if CHUNKSIZE==filesize and filesize is bigger than RAM ? use mmap()...
            is_there_data = any(data)
            digest.update(data)
        else:
            data = fh.read(CHUNKSIZE)
            is_there_data = any(data)
            digest.update(data)

            fh.seek(math.floor(filesize/2-CHUNKSIZE/2))
            data = fh.read(CHUNKSIZE)
            is_there_data |= any(data)
            digest.update(data)

            fh.seek(filesize-CHUNKSIZE)
            data = fh.read(CHUNKSIZE)
            is_there_data |= any(data)
            digest.update(data)
    if not is_there_data and (filesize<=3*CHUNKSIZE or check_zerofile(filename)):
        return 0  # File with size >0 but totally filled with zeros...
    return digest.intdigest() - (1<<63) # return integer rather than hexdigest because it is more efficient. "- (1<<63)" is there because SQLite3 unfortunately only supports signed 64 bits integers and doesn't support unsigned

def check_zerofile(filename):
    with open(filename,'rb') as fh:
        k = not any(fh.read())
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

def regmulti(regfile):
    regstr = ""
    with open(regfile) as fh:
        for reg in fh:
            reg=reg.replace("\n","")
            regstr += f'(?:{reg})|'
    regex = re.compile(regstr[:-1]) # FIXME: max length ?
    print(regex)
    return regex

def globmulti(globfile,var='path'):
    """Generate the 'where' part of an SQL query excluding all the entries in globfile"""
    globarr = []
    with open(globfile) as fh:
        for g in fh:
            g=g.replace("\n","")
            globarr.append(f"not {var} glob '{g}'")
    globstr = "(" + " and ".join(globarr) + ")"
    return globstr


######################################################
# DB class

class DDB():
    def __init__(self, dbname, domagic=False, resume=False, regignore=None, globignore=None,chunksize=FILE_HASH_CHUNKSIZE, prevdb=None):
        self.dbname=dbname
        self.update = os.path.exists(dbname)
        self.conn = sqlite3.connect(dbname)
        self.conn.create_function("get_parentdir_len", 1, lambda x: 0 if os.path.dirname(x)=='/' else len(os.path.dirname(x)))
        #self.conn.execute("PRAGMA temp_store = MEMORY") # "pragma query_only = ON" does not enable temp views...
        self.cur = self.conn.cursor()
        self.processedfiles = 0
        self.processedsize = 0
        self.reused = 0
        self.resume = resume
        self.curprev = None
        print((dbname,prevdb))
        if prevdb is not None and prevdb!=dbname:
            if self.update: sys.exit('Need a blank newdb when using prevdb !')
            self.prevdb = prevdb
            self.connprev = sqlite3.connect(prevdb)
            self.curprev = self.connprev.cursor()
        if self.update:
            tables = [k[0] for k in self.cur.execute("select name from sqlite_master where type='table'").fetchall()]
            if not 'entries' in tables:
                print('No table entries')
                sys.exit('Old DB schema. Migrate first !')
            self.curprev = self.conn.cursor()
            self.cur.execute("create temp table reviewed_entries (id integer unique)")
            #if resume==True:
            #    print('Looking for resume') # FIXME: make it also work to load the previous version of a db and only scan dirs with updated mtime
            #    mydirs = self.cur.execute("select path,size,hash,nsubfiles from entries where type='D'").fetchall()
            #    if len(mydirs)>0:
            #        print("Resuming from previous scan")
            #        self.dbcache_dirs = {k[0]:[k[1],k[2],k[3]] for k in mydirs}
                    #self.cur.execute("delete from entries where type in ('F', 'S') and not parentdir in (select path from entries where type='D')")
                    #emptyf = self.cur.execute("select count(*),sum(size) from files").fetchall()
                    #self.processedfiles=emptyf[0][0]
                    #self.processedsize=emptyf[0][1]
        else: self.createdb()
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

        self.regex = regmulti(regignore) if regignore else None
        self.globignore= globmulti(globignore) if globignore else ''
        self.chunksize=chunksize
        #print(f"Hash chunk size is {chunksize} bytes")
        #print(self.globignore)

    def createdb(self):
        print("Creating / resetting DB")
        with open("kindfs.sql", encoding='utf-8') as schema:
            self.cur.executescript(schema.read())

    def createindexes(self):
        print("\nCreating indexes")
        self.cur.executescript("""
            create index entries_parentdir_idx on entries(parentdir);
            create index entries_path_idx on entries(path);
            create index entries_name_idx on entries(name);
            create index entries_ext_idx on entries(extension);
            create index entries_size_idx on entries(size);
            create index entries_hash_idx on entries(hash);
            create index entries_depht_idx on entries(depht);""")

    def magicid(self, path, dofull=True, domime=True):
        """Compute 'magic' filetype from libmagic, insert it in DB (if not already there) and return the ID of that entry"""
        if self.domagic==False or (dofull==False and domime==False):
            return 0
        magictype = re.sub(', BuildID\\[sha1\\]=[0-9a-f]*','',magic.from_file(path)) if dofull else None
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
        if sync:   # For debug purposes, yet slower than the batch insert (even with pragmas and caching)
            self.cur.execute(f'insert or replace into entries values ({",".join("?" for k in vec)})', vec)
            return
        self.dbcache_insert.append(vec)
        mytime2=time.time()
        if mytime2-self.timer_insert>DB_COMMIT_PERIODICITY:
            self.sync_db()
            self.timer_insert=time.time() # Not 'mytime2' since sync_db() itself might take a few seconds, maybe more than DB_COMMIT_PERIODICITY
            #self.cur.execute(f'insert or replace into {table} values ({",".join("?" for k in vec)})', vec) #q = '(' + '?,' * (len(vec)-1) + '?)'

    def dirscan(self, bdir, init_path=None, parentdir=None, dirstat=None, dirlevel=0):
        """Recursively scan a dir/ (taking care of encoding issues), compute checksums and store metadata in the DB"""
        if isinstance(bdir,str):
            bdir=bytes(bdir, encoding='utf-8') # This avoids issues when walking through a filesystem with various encodings...
        def dbpath(path):
            if os.sep != '/': path=path.replace(os.sep, '/')
            return path.replace(init_path, '') if path!=init_path else "/"
        def printprogress():
            mytime2=time.time()
            if mytime2-self.timer_print>DISPLAY_PERIODICITY:
                k=dbpath(dir_printable)
                strprefix = f"Scanning: [{self.processedsize>>20} MB, {self.processedfiles} files, {self.processedfiles - self.reused} new] "
                ld=len(k) - (os.get_terminal_size()[0]-len(strprefix)-5) # -40 ?
                sys.stderr.write(f"\033[2K\r{strprefix}{colored('...','red')+k[ld:] if ld>0 else k}")
                sys.stderr.flush()
                self.timer_print=mytime2

        #print((bdir,processed,init_path,parentdir,self.mytime))
        dir,dir_printable = mydecode_path(bdir)
        if init_path==None: # root call (before recursion)
            init_path=dir.rstrip('/')
            print("\n==== Starting scan ====\n")
            self.cur.execute('insert or replace into dbsessions values (null, ?,?)', (int(self.timer_print), init_path))
            self.param_id=self.cur.lastrowid
        parentdir_len = len(dbpath(parentdir)) if parentdir!=None else 0
        curdir_len = len(dbpath(dir))

        if hasattr(self,'dbcache_dirs'): # Resume / speedup scan. FIXME: obsolete ?
            mypath=dbpath(dir_printable)
            if mypath in self.dbcache_dirs:
                mysize,myxxh,mysubfiles = self.dbcache_dirs[mypath]
                self.processedfiles+=mysubfiles
                self.processedsize+=mysize
                return mysize,myxxh
            #else: # FIXME: seems counter productive (sqlite bottleneck ?)
            #    refdb_alreadythere={k[0]:k[1] for k in self.cur_ref.execute("select path,size from files where parentdir=?", (dbpath(dir_printable),)).fetchall() }
        if self.resume:  # Must only be done if the underlying filesystem has not changed since previous aborted scan (if unsure, don't do a resume since it will skip all subdirectories that are assumed to be already scanned !)
            rs = self.cur.execute("select size,hash,nsubfiles_rec from entries where type='D' and path=? st_mtime=?", (dbpath(dir), int(dirstat.st_mtime))).fetchall()
            if len(rs)>0:
                return entrysize,dxxh,nsr

        dirsize=0 # size of current dir including subdirs
        dircontents = array('q') # Array of hashes for the contents of current dir. array('q') is more space-efficient than linked list, and better than numpy in this phase as it can easily grow without destroying/recreating the array
        dir_numfiles = 0
        dir_numdirs = 0
        dir_nsubfiles_rec = 0
        for entry in os.scandir(bdir):
            path,path_printable = mydecode_path(entry.path)
            name,name_printable = mydecode_path(entry.name)
            path_in_db = dbpath(path_printable)
            if not os.path.exists(path) or not os.access(path, os.R_OK):
                continue
            if entry.is_dir(follow_symlinks=False):
                #try:
                dirstat = entry.stat(follow_symlinks=False)
                entrysize,dxxh,nsr = self.dirscan(entry.path,init_path=init_path,parentdir=dir_printable,dirstat=dirstat,dirlevel=dirlevel+1)
                # Insertion in DB is below at dir toplevel (and this is a recursive call)
                dircontents.append(dxxh)
                dir_numdirs+=1
                dir_nsubfiles_rec += nsr
                #except:
                #    sys.stderr.write(f"\n=> Error in {path_printable}\n") # FIXME: log errors somewhere in DB
            elif entry.is_symlink():
                ltarget = os.readlink(path)
                lxxh = xxhash.xxh64(name + ' -> ' + ltarget).intdigest() - (1<<63)
                dircontents.append(lxxh)
                ext_len = path_in_db.rindex('.') if "." in path_in_db[curdir_len:] else None
                self.insert_db((
                    None,                               # id integer primary key autoincrement
                    'S',                                # type: symlink
                    path_in_db,                         # path
                    curdir_len,                         # parentdir_len
                    ext_len,                            # ext_len
                    None,                               # size
                    lxxh,                               # hash
                    None, None, None, None,             # magictype, nsubdirs, nsubfiles, nsubfiles_rec
                    ltarget,                            # symtarget
                    None,None,None,None,None,None,None, # struct stat is not needed
                    self.param_id                       # dbsession
                ))
                entrysize=0
                #dir_numfiles += 1 # FIXME: should we do it ?
                #dir_nsubfiles_rec += 1
            elif entry.is_file(follow_symlinks=False): # regular file. FIXME: sort by inode (like in https://github.com/pixelb/fslint/blob/master/fslint/findup) in order to speed up scanning ?
                filestat = entry.stat(follow_symlinks=False)
                entrysize = int(filestat.st_size)
                fxxh = None
                if self.curprev is not None:  # true both in case a prevdb is used, and in case of resume
                    rs = self.curprev.execute("select hash from entries where type='F' and path=? and size=? and st_mtime=?", (path_in_db, entrysize, int(filestat.st_mtime))).fetchall()
                    if len(rs)>0: fxxh = rs[0][0]
                if fxxh is None:
                    fxxh = xxhash_file(path, entrysize, chunksize=self.chunksize)
                else:
                    self.reused += 1
                ext_len = path_in_db.rindex('.') if "." in path_in_db[curdir_len:] else None
                mymagicid = self.magicid(path)
                self.insert_db((
                    None,                             # id integer primary key autoincrement
                    'F',                              # type: file
                    path_in_db,                       # path
                    curdir_len,                       # parentdir_len
                    ext_len,                          # ext_len
                    entrysize,                        # size
                    fxxh,                             # hash
                    mymagicid,                        # magictype
                    None, None, None, None,           # nsubdirs, nsubfiles, nsubfiles_rec, symtarget
                    int(filestat.st_mtime), filestat.st_mode, filestat.st_uid, filestat.st_gid, filestat.st_ino, filestat.st_nlink, filestat.st_dev-(1<<63),
                    self.param_id                     # dbsession
                ))
                dircontents.append(fxxh) #bisect.insort(dircontents[dir], xxh)
                self.processedfiles+=1
                self.processedsize+=entrysize
                dir_numfiles += 1
                dir_nsubfiles_rec += 1
            else:
                continue # e.g. named pipes...
                #print("__error__: " + path)
                #entrysize=0
            dirsize += entrysize
            printprogress()
        dircontents = array('q', sorted(dircontents))
        dxxh = 0 if dirsize==0 else xxhash.xxh64(dircontents.tobytes()).intdigest() - (1<<63)
        #bisect.insort(dircontents[os.path.dirname(dir)], dirxxh)
        if dirstat==None:
            dirstat = os.lstat(dir)
        path_in_db = dbpath(dir_printable)
        #if self.curprev is not None:
        #    rs = self.curprev.execute("select size,hash,nsubfiles_rec from entries where type='D' and path=? and size=? and st_mtime=?", (path_in_db, dirsize, int(filestat.st_mtime))).fetchall()
        #    if len(rs)>0: entrysize,dxxh,nsr = rs[0]

        self.insert_db((
            None,                             # id integer primary key autoincrement
            'D',                              # type: dir
            path_in_db,                       # path
            parentdir_len,                    # parentdir_len
            None,                             # ext_len
            dirsize,                          # size
            dxxh,                             # hash
            None,                             # magictype
            dir_numdirs,                      # nsubdirs
            dir_numfiles,                     # nsubfiles
            dir_nsubfiles_rec,                # nsubfiles_rec
            None,                             # symtarget
            int(dirstat.st_mtime), dirstat.st_mode, dirstat.st_uid, dirstat.st_gid, None ,dirstat.st_nlink, dirstat.st_dev-(1<<63),
            self.param_id                     # dbsession
        ))
        return dirsize,dxxh,dir_nsubfiles_rec

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

    def compute_cachedups(self,basedir=""):
        cur = self.conn.cursor()
        print("\nComputing duplicates...")
        wbasedir = f"where path like '{basedir}/%'" if basedir!='' else ''
        wbasedir2 = f"and path like '{basedir}/%'" if basedir!='' else ''
        cur.executescript(f'''
            drop table if exists cachedups_h;
            create table cachedups_h (hash integer, size integer, ndups integer,type char(1));
            insert into cachedups_h select hash,size,count(*),type from entries {wbasedir} group by hash,size,type having count(*)>1 and size>0;

            drop table if exists cachedups;
            create table cachedups (entry_id integer not null, size integer, ndups integer, totaldupsize integer GENERATED ALWAYS AS (size*(ndups-1)) VIRTUAL);
            create index cachedups_totaldupsize_idx on cachedups(totaldupsize);
            create index cachedups_entry_id_idx on cachedups(entry_id);
            create index cachedups_size_idx on cachedups(size);
            insert into cachedups select entries.id,entries.size,ndups from entries inner join cachedups_h
                on entries.hash=cachedups_h.hash where entries.size=cachedups_h.size {wbasedir2} and entries.type=cachedups_h.type
                order by entries.size desc;
        ''')

    def get_rec_pcdup(self, dir, entry_id=None):
        # compute the % of dups within dirs
        cur = self.conn.cursor()
        if entry_id is None:
            cur.execute("create table cachedups_d (entry_id integer not null, szdup integer, ndupsubs integer)")
            entry_id = cur.execute("select id from entries where path=?", (dir,)).fetchall()[0][0]
        sz_n_dup = 0 + 0j
        rs = cur.execute("select id, path, type, size, nsubfiles_rec from entries where parentdir=?",(dir,))
        for rowid, path, entrytype, size, nrec in rs:
            szdup_entry = cur.execute("select size from cachedups inner join entries on entry_id=entries.id where path=?", (path,)).fetchall()[0][0]
            if szdup_entry is not None:
                sz_n_dup += szdup_entry + 1j*(nrec if entrytype == "D" else 1)
            elif entrytype == "D":
                sz_n_dup += self.get_rec_pcdup(path, entry_id=rowid)

        cur.execute("insert into cachedups_d (id, szdup, ndupsubs) values (?,?)", entry_id, sz_n_dup.real, sz_n_dup.imag)
        return sz_n_dup

    def compute_cachedups_dpartial(self,basedir=""):
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        wbasedir = f"where path like '{basedir}/%'" if basedir!='' else ''
        orderbysize=True
        #orderby = "totaldupsize" if orderbysize else "nsubfiles_rec"
        orderby = "entries.size" if orderbysize else "nsubfiles_rec"
        rs = cur.execute(f"select type,path,cachedups.size,hash,ndups,parentdir,nsubfiles_rec from cachedups inner join entries on entry_id=entries.id where cachedups.size>0 {wbasedir} order by {orderby} desc") #where not parentdir in (select path from cachedups)
        for type,path,size,hash,ndups,parentdir,nsubfiles_rec in rs:
            rs2 = cur2.execute("select entry_id from cachedups inner join entries on entry_id=entries.id where parentdir=?", parentdir).fetchall()[0]
            if len(rs2):
                continue

    def compute_cachedups_d(self,basedir=""): # FIXME: Experimental function supporting getincluded()
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        #cur3 = self.conn.cursor()
        cur.executescript(f'''
            drop table if exists cachedups_d;
            create table cachedups_d (entry_id integer not null, size integer, nsubdups integer);
            create index cachedups_d_entry_id_idx on cachedups_d(entry_id);
            create index cachedups_d_size_idx on cachedups_d(size);
        ''')
        cachedups_d = defaultdict(int)
        n=0 ; ncount = cur.execute("select count(*) from cachedups_h where type='F'").fetchall()[0][0]
        rs = cur.execute("select hash,ndups from cachedups_h where type='F' and hash!=0 and hash!=-1<<63 and size>0")  # and ndups<1000
        for hash,ndups in rs:
            n+=1
            paths=[k[0] for k in cur2.execute("select path from entries where type='F' and hash=?",(hash,)).fetchall()]
            for path in paths:
                dir_tmp = os.path.dirname(path)
                #pdir_isdup = cur3.execute("select count(*) from cachedups inner join entries on entry_id=entries.id where path=?", (dir_tmp,)).fetchall()[0][0]
                while dir_tmp!='/':
                    if any([not dir_tmp in k for k in paths]):
                        cachedups_d[dir_tmp] += 1
                        dir_tmp = os.path.dirname(dir_tmp)
                    else: break
                #sys.stderr.write(f".");sys.stderr.flush()
            sys.stderr.write(f"\033[2K\r{int(100*n/ncount)}%");sys.stderr.flush()
        #rs = cur.execute("select path,hash from cachedups inner join entries on entry_id=entries.id where type='F'")
        #for path,hash in rs:
            #path_tmp = os.path.dirname(path)
            #while path_tmp!='/':
                #cachedirs_dupratio[path_tmp] += 1
                #path_tmp = os.path.dirname(path_tmp)
        print("Phase 3")
        cur.executemany("insert into cachedups_d select id,size,? from entries where path=?", [(v,k) for k,v in cachedups_d.items()])
        self.conn.commit()
        # select size,ndups,path,type,hash from cachedups where not parentdir in (select path from cachedups) order by size desc

    def showdups(self,basedir="",mountpoint="",nres=None,orderby="totaldupsize"):
        """Main function to display the duplicate entries (file or dirs) sorted by decreasing size"""
        # orderby = "totaldupsize" | "nsubfiles_rec" | "entries.size" | "cachedups.size"
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        tables = [k[0] for k in self.cur.execute("select name from sqlite_master where type='table'").fetchall()]
        if not 'cachedups' in tables:
            self.compute_cachedups()
        wbasedir = f"and path like '{basedir}/%'" if basedir!='' else "" #"where type='D'"
        limit_nres = f'limit {int(nres)}' if nres else ''
        rs = cur.execute(f"select type,path,cachedups.size,hash,ndups,parentdir,nsubfiles_rec from cachedups inner join entries on entry_id=entries.id where cachedups.size>0 {wbasedir} order by {orderby} desc {limit_nres}") #where not parentdir in (select path from cachedups)
        for ftype,path,size,hash,ndups,parentdir,nsubfiles_rec in rs:
            pdir_isdup = cur2.execute("select count(*) from cachedups inner join entries on entry_id=entries.id where path=?", (parentdir,)).fetchall()[0][0]
            path_real = mountpoint+path
            if mountpoint!='' and mountpoint!=None and not os.path.exists(mountpoint+path):
                path_real = colored(path_real, 'red')
            elif pdir_isdup>0:
                path_real = colored(path_real, 'cyan') + colored(' [parent dir already in dups]', 'yellow')
            elif 'syncthing' in path_real or 'lost+found' in path_real:
                path_real = colored(path_real, 'cyan')

            print(colored(f"{ftype} 0x{hash+(1<<63):0>16x}, {ndups} * {size>>20} Mo | {nsubfiles_rec} files : ", 'yellow') + path_real)
            #print(colored(f"{ftype} {hash+(1<<63)}, {ndups} * {size} | {nsubfiles_rec} files : ", 'yellow') + path_real)

    def compute_partial_dup_dirs(self, dir, depth=0, direntry_id=None):
        """Recursive call to compute table dir_containing_dups which further enables to show the % of duplicates within each dir"""
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        if depth==0:
            print('__reset')
            #tables = [k[0] for k in self.cur.execute("select name from sqlite_master where type='table'").fetchall()]
            #if not 'cachedups_d' in tables:
            cur.execute("drop table if exists dir_containing_dups")
            cur.execute("create table dir_containing_dups (entry_id integer not null, szdup integer, ndupsubs integer)")
            direntry_id,totsize = cur.execute("select id,size from entries where path=?", (dir,)).fetchall()[0]
            self.totsize = totsize
            self.totseen = 0
            #cur.execute("insert into dir_containing_dups (entry_id, szdup, ndupsubs) values (1, 2, 3)")
        rs = cur.execute("select id,path,size,type,nsubfiles_rec from entries where parentdir=? and type!='S'", (dir,))
        dupsize=0
        ndups=0
        for entry_id, path, size, entrytype, nsubfiles_rec in rs:
            #print((entry_id, path, size, entrytype))
            isdup = cur2.execute("select entry_id from cachedups where entry_id=?", (entry_id,)).fetchall()
            if len(isdup)>0:
                dupsize += size
                ndups+=1 if entrytype=='F' else nsubfiles_rec
                self.totseen += size
            elif entrytype=='D':
                tmp0, tmp1= self.compute_partial_dup_dirs(path, depth+1, entry_id)
                dupsize += tmp0
                ndups += tmp1
            else: # 'F'
                self.totseen += size

            mytime2=time.time()
            if mytime2-self.timer_print>DISPLAY_PERIODICITY:
                sys.stderr.write(f"\033[2K\rComputing dir duplicates : {100*self.totseen//self.totsize} %")
                sys.stderr.flush()
                self.timer_print=mytime2
        if dupsize >0:
            #print((direntry_id, dupsize, ndups))
            cur.execute("insert into dir_containing_dups (entry_id, szdup, ndupsubs) values (?, ?, ?)", (direntry_id, dupsize, ndups))

        return dupsize, ndups

    def show_partial_dup_dirs(self,basedir="",mountpoint="",nres=None,orderby="szdup desc"): #orderby="pcdup desc,szdup desc"
        """Main function to display the duplicate entries (file or dirs) sorted by decreasing size"""
        # orderby = "totaldupsize" | "nsubfiles_rec" | "entries.size" | "cachedups.size"
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        wbasedir = f"and path like '{basedir}/%'" if basedir!='' else "" #"where type='D'"
        limit_nres = f'limit {int(nres)}' if nres else ''
        rs = cur.execute(f"select path,entries.size, nsubfiles_rec, round(100*szdup/entries.size) pcdup, round(100*ndupsubs/nsubfiles_rec) pcfiles from dir_containing_dups inner join entries on entry_id=entries.id where pcdup > 80 {wbasedir} order by {orderby} {limit_nres}") #where not parentdir in (select path from cachedups)
        for path, size, nsubfiles_rec, pcdup, pcfiles in rs:
            print(colored(f"{pcdup} % * {size>>20} Mo | {pcfiles} % * {nsubfiles_rec} files : ", 'yellow') + path)

    def show_same_inode(self,basedir="",nres=None):
        """Same as showdups() but only return entries with identical inodes"""
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        limit_nres = f'limit {int(nres)}' if nres else ''
        rs = cur.execute(f"select size,path,hash,st_ino,parentdir from entries where st_ino in (select st_ino from entries group by st_ino having count(*)>1 and type='F') order by size desc {limit_nres}")
        for size,path,hash,inode,parentdir in rs:
            pdir_isdup = cur2.execute("select count(*) from cachedups where path=?", (parentdir,)).fetchall()[0][0]
            path_real = basedir+path
            if basedir!='' and basedir!=None and not os.path.exists(basedir+path):
                path_real = colored(path_real, 'red')
            elif pdir_isdup>0:
                path_real = colored(path_real, 'cyan') + colored(' [parent dir already in dups]', 'yellow')
            elif 'syncthing' in path_real or 'lost+found' in path_real:
                path_real = colored(path_real, 'cyan')
            print(colored(f"{inode} 0x{hash+(1<<63):0>16x}, {size>>20} Mo : ", 'yellow') + path_real)

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

    def walk(self,init_path=''): # FIXME: self.init_path ?
        """Same function as os.walk() for filesystems"""
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        for res in cur.execute("select path from entries where type='D' and path like ? order by path", (init_path+'/%',)):
            dir=res[0]
            dirs = [k[0] for k in cur2.execute("select name from entries where type='D' and parentdir=?",(dir,))]
            files = [k[0] for k in cur2.execute("select name from entries where parentdir=? and (type='F' or type='S')",(dir,))]
            #files.append([k[0] for k in cur2.execute('select name from symlinks where parentdir=?',(dir,))])
            yield dir,dirs,files

    def grepext(self, wordlist, ext='.txt', init_path='', mountpoint='', case_insensitive=True):
        cur = self.conn.cursor()
        count = cur.execute("select count(path) from entries where type='F' and name like ?", ('%'+ext,)).fetchall()[0][0]
        k=0
        pct=0
        print(wordlist)
        if case_insensitive:
            for idx in range(len(wordlist)):
                wordlist[idx]=wordlist[idx].lower()
        for res in cur.execute("select path from entries where type='F' and name like ?", ('%'+ext,)):
            path=res[0]
            try: btext = open(mountpoint+'/'+path,"rb").read()
            except (FileNotFoundError,PermissionError): print('\033[2K\r__error file__: '+path)
            for w in wordlist:
                try: text = btext.decode()
                except UnicodeDecodeError: text = btext.decode(encoding="latin1")
                if case_insensitive: text=text.lower()
                #if w.encode() in open(bytes(mountpoint+'/'+path, encoding='utf-8'),"rb").read():
                if w in text:
                    print('\033[2K\r'+path)
            k+=1
            pct = 100*k//count
            sys.stderr.write(f"\033[2K\r{pct} % : {k} / {count}")

    def dumpdir(self, adir=''):
        """Dumps the contents of a dir (and all subdirs) with hash and size"""
        cur = self.conn.cursor()
        for line in cur.execute("select path,xxh64be,size from dirs where path like ? order by path", (adir+'/%',)):
            (path,xxh64be,size) = line
            print("0x%016x, %d : %s" % (xxh64be+(1<<63), size, path.replace(adir,'')))

    def dbgsize(self):
        cur = self.conn.cursor()
        return cur.execute("select sum(size) from files").fetchall()[0][0]

    def isincluded(self, path_test, path_ref, otherddbfs=None, docount=True,display_included=False,display_notincluded=True,basedir="", checkfs=True, raw=False):
        """Checks whether every file under path_test/ (and subdirs) has a copy somewhere in path_ref (regardless of the directory structure in path_ref/ )"""
        def fullcheck(path0, pathlist):
            for p in pathlist:
                #print(f"\nchecking {path0} | {p}")
                if os.path.exists(path0) and filecmp.cmp(path0, p, shallow=False):
                    return True
            return False
        cur = self.conn.cursor()
        if otherddbfs:
            conn2 = sqlite3.connect(otherddbfs)
            cur2 = conn2.cursor()
        else:
            cur2 = self.conn.cursor()

        ignorestr = f'and {self.globignore}' if self.globignore else ''
        mycount=cur.execute(f"select count(*) from (select path from entries where type='F' and size>0 and path like ? order by id)", (path_test+"/%",)).fetchone()[0] if docount else 1  # FIXME: putting {ignorestr} here would make the result accurate but would significantly slow-down the query... I think it is OK if the number/progressbar is overestimated
        rs = cur.execute(f"select name,hash,size,path from entries where type='F' and size>0 and path like ? {ignorestr} order by id", (path_test+'/%',))
        k=1
        if not rs or mycount==0:
            print('No results !')
        if basedir=='':
            checkfs=False
        for line in rs:
            name,xxh,size,path=line
            if xxh==0 or size==0: # skip null files or files made of zeros
                continue
            if checkfs and not os.path.exists(basedir+path):
                if not raw:
                    sys.stderr.write(colored(f"\033[2K\r{basedir+path} ({size>>20} Mo) is deleted\n",'red'))
                continue
            if not otherddbfs and path_ref=='':
                rs2=cur2.execute("select path from entries where type='F' and hash=? and size=? and not path like ?", (xxh, size, path_test+'/%')).fetchall()
            elif otherddbfs:
                #rs2=cur2.execute("select path from files where xxh64be=? and size=? and path like ?", (xxh, size, path_ref+'/%')).fetchall()
                rs2=cur2.execute("select path from entries where type='F' and hash=? and size=? and path like ? limit 1", (xxh, size, path_ref+'/%')).fetchall()
            else:
                rs2=cur2.execute("select path from entries where type='F' and hash=? and size=? and path!=? and path like ?", (xxh, size, path, path_ref+'/%')).fetchall()
                #rs2=cur2.execute("select path from files where xxh64be=? and size=? and path!=?", (xxh, size, path)).fetchall()

            if not rs2:
                if display_notincluded:
                    if(raw): print(path)
                    else:
                        sys.stderr.write(f"\033[2K\r")
                        #print(colored(f"No equivalent for {xxh+(1<<63):0>16x}, {size>>20} Mo : {self.dbname}:{path}",'yellow'))
                        print(colored(f"No equivalent for {xxh+(1<<63)}, {size>>20} Mo : {path}",'yellow'))
            else:
                if checkfs and not any([os.path.exists(basedir+dup[0]) for dup in rs2[:20]]):
                    # Even if there are results, we check here whether they still exist (when checkfs==True) in case they might have been deleted since previous scan
                    # FIXME: we restrict to the 20 first dups as otherwise there is a performance issue for rare cases with large number of results (e.g. small system/compilation files that are identical among many projects). But this workaround is suboptimal.
                    if display_notincluded:
                        if(raw): print(path)
                        else:
                            sys.stderr.write(f"\033[2K\r")
                            print(colored(f"No equivalent anymore for ({size>>20} Mo) : {path}",'red'))
                elif display_included:  # in that case we only display results for dirA that _are_ in dirB
                    if checkfs and fullcheck(basedir+path, [basedir+z[0] for z in rs2])==False:
                        continue
                    if(raw): print(path)
                    else:
                        sys.stderr.write(f"\033[2K\r")
                        print(colored(f"{path} ({size>>20} Mo) has the equivalents: {rs2}",'green'))

            if not raw:
                mytime2=time.time()
                if mytime2-self.timer_print>0.05:
                    sys.stderr.write(f"\033[2K\rScanning: [{k} / {mycount} entries, {int(100*k/mycount)}%] ")
                    sys.stderr.flush()
                    self.timer_print=mytime2
                k+=1
        if otherddbfs:
            conn2.close()

    def diff(self,dir1,dir2):
        self.isincluded(dir1,dir2)
        self.isincluded(dir2,dir1)

    def getincluded(self,basedir=''):
        cur = self.conn.cursor()
        cur2 = self.conn.cursor()
        rs = cur.execute("select path,nsubfiles_rec,size from entries where type='D' and path like ? order by size desc", (basedir+'/%',))
        #rs = cur.execute("select path,size from entries where type='D' and path like ?", (basedir+'/%',))
        for parentdir,nsubfiles_rec,size in rs:
            #nsubfiles_rec = make_nsubfiles_rec(parentdir)
            dir_isdup = cur2.execute("select count(*) from cachedups where path=?", (parentdir,)).fetchall()[0][0]
            if dir_isdup:
                print(f"{parentdir} is dup")
                continue
            nsubfiles_rec_dups = cur2.execute("select count(*) from cachedups where type='F' and path like ?", (parentdir+'/%',)).fetchall()[0][0]
            print(f"{size>>20} MB, {100*nsubfiles_rec_dups/nsubfiles_rec:.1f}% dups : {parentdir}")

    def nsubfiles_rec(self,adir,k=0):
        if adir=='/' or adir=='':
            return None
        #rs1=cur_tmp.execute("select sum(nsubfiles) ns from entries where path like ? and type='D'", (adir+'%',)).fetchall()[0][0]
        cur = self.conn.cursor()
        nfiles,ndirs,nfiles_r=cur.execute("select nsubfiles,nsubdirs,nsubfiles_rec from entries where path=? and type='D'", (adir,)).fetchall()[0]
        if nfiles_r!=None:
            return nfiles_r
        if ndirs>0:
            rs = cur.execute("select path,nsubfiles,nsubdirs from entries where parentdir=? and type='D'", (adir,)).fetchall()
            for path,nsubfiles,nsubdirs in rs:
                nfiles += self.nsubfiles_rec(path,k+1) if nsubdirs>0 else nsubfiles
        cur.execute("update entries set nsubfiles_rec=? where path=?",(nfiles,adir))
        return nfiles

    def schema2(self): # unfinished. Problem: no details of the contents of virtual columns
        cur = self.conn.cursor()
        rs = cur.execute("select name from sqlite_master where type='table' order by name").fetchall()
        tables = [k[0] for k in rs if k[0] is not None]
        for table in tables:
            rs = cur.execute(f"select * from pragma_table_xinfo('{table}') order by name").fetchall()

    def schema(self, dosort=True):
        def schemasort(a): # make the schema sorted and determinist for future comparisons
            if not dosort:
                return a
            a = re.sub("--.*", "", a) # FIXME: it was nice to have a -- version: XXX in SQL comments. This line discards it
            a = re.sub("\n *", "", a)
            table = re.sub("(CREATE TABLE [^ \\(]*).*", "\\1",a)
            a = re.sub("CREATE TABLE [^\\(]*\\(", "", a)[:-1]
            a = a.replace(', ',',')
            c = 0 ; out = ""
            for k in a: # we need to distinguish ',' separating fields and ',' as part of functions...
                if k=='(': c+=1
                elif k==')': c-=1
                elif k==',' and c>0: k=';'
                out += k
            alist = [k.replace(';', ',') for k in out.split(',')]
            a = ",\n\t".join(sorted(alist))
            return table + '(\n\t' + a + '\n)'
        cur = self.conn.cursor()
        rs = cur.execute("select sql from sqlite_master where type='table' order by name").fetchall()
        schema_text = ";\n".join([schemasort(k[0]) for k in rs if k[0] is not None])
        schema_hash = xxhash.xxh64(schema_text).hexdigest()
        return schema_text, schema_hash


############################################
# Main

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("dbfile", help="DB path")
    subparsers = parser.add_subparsers(dest="subcommand", required=True)

    parser_scan = subparsers.add_parser('scan', help="Scan directory")
    parser_scan.add_argument("path", help="path to scan")
    parser_scan.add_argument("--resetdb", "-R", help="Reset DB", action='store_true', default=False)
    parser_scan.add_argument("--previousdb", "-p", help="Previous DB (speed up scan)", default=None)
    parser_scan.add_argument("--chunksize", "-C", help="file chunk size in bytes for xxhash (default is 1 MB)", default=FILE_HASH_CHUNKSIZE>>10)
    # FIXME: add option to use a previous db, and skip dirs (+ copy the previous db contents for those subdirs) when mtime has not changed

    parser_mount = subparsers.add_parser('mount')
    parser_mount.add_argument("mountpoint", help="Mount point")

    parser_isincluded = subparsers.add_parser('isincluded', help="Check whether all files in dirA/ are included in dirB/")
    parser_isincluded.add_argument('dirA', help="source dir")
    parser_isincluded.add_argument('dirB', help="dest dir")
    parser_isincluded.add_argument("--otherdb", "-o", help="otherdb", default=None)
    parser_isincluded.add_argument("--mountpoint", "-m", help="mountpoint for checking whether files are still present", default='')
    parser_isincluded.add_argument("--display_included", "-i", help="Display files from dirA that are in dirB", action='store_true', default=False)
    parser_isincluded.add_argument("--display_notincluded", "-n", help="Display files from dirA that are not in dirB", action='store_true', default=False)
    #parser_isincluded.add_argument("--raw", "-r", help="Display files from dirA that are not in dirB", action='store_true', default=False)
    parser_isincluded.add_argument("--globignore", "-g", help="Glob file to ignore results", default=None)

    parser_comparedb = subparsers.add_parser('comparedb', help="Compare two DB")
    parser_comparedb.add_argument('otherdb', help="DB to compare with")
    parser_comparedb.add_argument("--globignore", "-z", help="Glob file to ignore results", default=None)

    parser_diff = subparsers.add_parser('diff', help="Show diffs between dirA/ and dirB/")
    parser_diff.add_argument('dirA', help="source dir")
    parser_diff.add_argument('dirB', help="dest dir")

    parser_dump=subparsers.add_parser('dump', help="dump DB")
    parser_dump.add_argument("--basedir", "-b", help="Basedir", default='')

    subparsers.add_parser('computehash', help="Compute hash")
    subparsers.add_parser('check_zerofile', help="Check whether file is made only of zeros (e.g. corrupted)")

    parser_schema = subparsers.add_parser('schema', help="Print DB schema")
    parser_schema.add_argument("--sql", "-s", help="Display SQL schema", action='store_true', default=False)
    parser_schema.add_argument("--hash", "-n", help="Display schema hash", action='store_false', default=True)

    subparsers.add_parser('compute_cachedups', help="Compute cachedups")
    parser_showdups = subparsers.add_parser('showdups', help="show duplicates")
    parser_showdups.add_argument("--mountpoint", "-m", help="mountpoint for checking whether files are still present", default='')
    parser_showdups.add_argument("--basedir", "-b", help="Basedir", default='')
    parser_showdups.add_argument("--limit", "-l", help="Max number of results", default=None)
    parser_showdups.add_argument("--orderby", "-o", help="indiv_size | total_size | num_subfiles", default="total_size")

    subparsers.add_parser('compute_partial_dup_dirs', help="Compute partial dup dirs")
    parser_showpartialdups = subparsers.add_parser('show_partial_dup_dirs', help="show duplicates")
    parser_showpartialdups.add_argument("--mountpoint", "-m", help="mountpoint for checking whether files are still present", default='')
    parser_showpartialdups.add_argument("--basedir", "-b", help="Basedir", default='')
    parser_showpartialdups.add_argument("--limit", "-l", help="Max number of results", default=None)
    parser_showpartialdups.add_argument("--orderby", "-o", help="indiv_size | total_size | num_subfiles", default="total_size")

    parser_grep = subparsers.add_parser('grep', help="grep text")
    parser_grep.add_argument("--mountpoint", "-m", help="mountpoint", default='')
    parser_grep.add_argument("--wordlist", "-w", help="mountpoint", nargs="+", required=True)

    # Legacy
    parser_dupfiles = subparsers.add_parser('dupfiles', help="show duplicate files")
    parser_dupfiles.add_argument("--mountpoint", "-m", help="mountpoint for checking whether files are still present", default=None)
    parser_dupfiles.add_argument("--limit", "-l", help="Max number of results", default=None)
    parser_dupdirs = subparsers.add_parser('dupdirs', help="show duplicate dirs")
    parser_dupdirs.add_argument("--mountpoint", "-m", help="mountpoint for checking whether files are still present", default=None)
    parser_dupdirs.add_argument("--limit", "-l", help="Max number of results", default=None)

    parser_inodes = subparsers.add_parser('inodes', help="show duplicate dirs")
    parser_inodes.add_argument("--mountpoint", "-m", help="mountpoint for checking whether files are still present", default=None)
    parser_inodes.add_argument("--limit", "-l", help="Max number of results", default=None)

    parser_getincluded = subparsers.add_parser('getincluded', help="test")
    parser_getincluded.add_argument("--basedir", "-b", help="Basedir", default='')

    parser_testreg = subparsers.add_parser('testreg', help="test")
    parser_testreg.add_argument("teststring", default="")

    args = parser.parse_args()

    if args.subcommand=='scan':
        if args.resetdb:
            os.remove(args.dbfile)
            #ddb.createdb()
            #ddb.conn.commit()
        ddb=DDB(args.dbfile, resume=False, chunksize=int(args.chunksize)<<10, prevdb = args.previousdb)
        try:
            ddb.dirscan(args.path)
            ddb.createindexes()
            ddb.sync_db()
            ddb.compute_cachedups()
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
        ddb=DDB(args.dbfile, globignore=args.globignore)
        if not (args.display_notincluded or args.display_included):
            print('Choose -n or -i !')
            exit()
        ddb.isincluded(args.dirA, args.dirB,
                       otherddbfs=args.otherdb, basedir=args.mountpoint,
                       display_included=args.display_included,
                       display_notincluded=args.display_notincluded, raw=False)
    elif args.subcommand=='diff':
        ddb=DDB(args.dbfile)
        ddb.diff(args.dirA, args.dirB)
    elif args.subcommand=='dupdirs':
        ddb=DDB(args.dbfile)
        ddb.compute_dupdirs(basedir=args.mountpoint, nres=args.limit)
    elif args.subcommand=='dupfiles':
        ddb=DDB(args.dbfile)
        ddb.compute_dupfiles(basedir=args.mountpoint, nres=args.limit)
    elif args.subcommand=='comparedb':
        print(f"Files from {args.dbfile} that are not in {args.otherdb} (i.e. deleted files)")
        ddb=DDB(args.dbfile, globignore=args.globignore)
        ddb.isincluded('', '', otherddbfs=args.otherdb, basedir='', checkfs=False)
        #print(f"\n_________\nFiles from {args.otherdb} that are not in {args.dbfile} (i.e. new files)")
        #ddb=DDB(args.otherdb)
        #ddb.isincluded('', '', otherddbfs=args.dbfile, basedir='', checkfs=False)
    elif args.subcommand=='computehash':
        filestat = os.stat(args.dbfile)
        entrysize = int(filestat.st_size)
        fxxh = xxhash_file(args.dbfile, entrysize)
        print(f"0x{fxxh+(1<<63):0>16x}, {fxxh+(1<<63)} {fxxh}, {entrysize>>20} Mo : {args.dbfile}")
    elif args.subcommand=='check_zerofile':
        print(check_zerofile(args.dbfile))
    elif args.subcommand=='schema':
        ddb=DDB(args.dbfile)
        schema,shash = ddb.schema()
        if args.sql: print(schema)
        if args.hash: print(f"Schema hash: {shash}")
    elif args.subcommand=='compute_cachedups':
        ddb=DDB(args.dbfile)
        ddb.compute_cachedups()
    elif args.subcommand=='compute_partial_dup_dirs':
        ddb=DDB(args.dbfile)
        ddb.compute_partial_dup_dirs('/')
        ddb.conn.commit()
        ddb.conn.close()
    elif args.subcommand=='show_partial_dup_dirs':
        ddb=DDB(args.dbfile)
        ddb.show_partial_dup_dirs(basedir=args.basedir, mountpoint=args.mountpoint, nres=args.limit)
    elif args.subcommand=='showdups':
        ddb=DDB(args.dbfile)
        my_order = {"indiv_size": "entries.size", "total_size": "totaldupsize", "num_subfiles": "nsubfiles_rec"} # "cachedups.size"
        ddb.showdups(basedir=args.basedir, mountpoint=args.mountpoint, nres=args.limit, orderby=my_order[args.orderby])
    elif args.subcommand=='inodes':
        ddb=DDB(args.dbfile)
        ddb.show_same_inode(basedir=args.mountpoint, nres=args.limit)
    elif args.subcommand=='getincluded':
        ddb=DDB(args.dbfile)
        ddb.getincluded(basedir=args.basedir)
    elif args.subcommand=='testreg':
        regex = regmulti(args.dbfile)
        print(re.match(regex,args.teststring))
    elif args.subcommand=='grep':
        ddb=DDB(args.dbfile)
        ddb.grepext(wordlist=args.wordlist, mountpoint=args.mountpoint)
    print()
