#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Feb 29 12:13:23 2020

@author: adrien
"""

import sqlite3,xxhash
import fnmatch
import math
import os,sys
import bisect
import array
import numpy as np
from collections import defaultdict

def xxhash_file(filename, filesize=None): # (1<<12)
    CHUNKSIZE=1024<<10 # 8 Mo chunk size
    if filesize==None:
        filesize=int(os.stat(filename).st_size)
    digest = xxhash.xxh64()
    #digest.update(filesize)
    #digest.update(filename)
    with open(filename,'rb') as fh:
        if(filesize<=3*CHUNKSIZE):
            digest.update(fh.read())
        else:
            digest.update(fh.read(CHUNKSIZE))
            fh.seek(math.floor(filesize/2-CHUNKSIZE/2))
            digest.update(fh.read(CHUNKSIZE))
            fh.seek(filesize-CHUNKSIZE)
            digest.update(fh.read(CHUNKSIZE))
    return digest.intdigest() - (1<<63)

class progresswalk:
    """Progress indicator for os.walk""" # The implementation may look complex, but it's because it tries to put the right "weigth" to dirs according to how deep they are in the filesystem
    def __init__(self, init_path):
        self.init_path = init_path
        self.init_depth = init_path.count('/')
        self.numdirs = [0+0j]
        self.numfiles=0+0j

    def update(self, dir, dirs, files):
        # numdirs[] is processed as a "polynom". It is using complex numbers in order to avoid using 2 lists: real part is total number of dirs, and imag part is number of processed dirs
        current_depth = dir.count('/') - self.init_depth
        if len(self.numdirs) < current_depth+2:
            self.numdirs.append(0+0j)
        self.numdirs[current_depth+1] += len(dirs)
        walkedRatio=0
        # compact the "polynom" numdirs with each "digit" in 0-9, and fit it into a "normal" integer
        for i in range(1, len(self.numdirs)-2): # [1:len(numdirs)-2] because the first value is 0 and the last value may be 0, and we want to avoid division by 0 !
            walkedRatio = walkedRatio*10 + int((9*self.numdirs[i].imag)/self.numdirs[i].real)
        completion = (100*walkedRatio) / (10**(len(self.numdirs)-3))
        self.numdirs[current_depth] += 1j
        #sys.stderr.write("\rScanning: [%d %%]   %s" % (completion,str(self.numdirs))) # self.init_path
        sys.stderr.write("\rScanning: [%d %%]" % (completion,)) # self.init_path

    def update2(self, dir, dirs, files):
        self.numfiles += len(files)
        completion=100*int(self.numfiles.imag/self.numfiles.real)
        sys.stderr.write("\rScanning: [%d %%]" % (completion,)) # self.init_path

    def updatef(self):
        self.numfiles += 1j

def createdb(dbfilename):
    with sqlite3.connect(dbfilename) as conn:
        cur = conn.cursor()
        cur.executescript('''
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
        ''')
            # PRAGMA main.page_size = 4096;
            # PRAGMA main.cache_size=10000;
            # PRAGMA main.locking_mode=EXCLUSIVE;
            # PRAGMA main.synchronous=NORMAL;
            # PRAGMA main.journal_mode=WAL;
            # PRAGMA main.cache_size=5000


def scandir(dbfilename, init_path, totalsize):
    #progress = progresswalk(init_path)
    processedsize=0
    processedfiles=0
    option_excludelist=[]
    dirsizes = defaultdict(int)
    dircontents = {}
    with sqlite3.connect(dbfilename) as conn:
        cur = conn.cursor()
        for (dir, dirs, files) in os.walk(init_path): # , topdown=False
            dircontents[dir] = array.array('q')
            #dircontents[dir] = np.array([],dtype=np.int64)
            #progress.update(dir, dirs, files)
            for excludetest in option_excludelist:
                if fnmatch.fnmatch(dir, excludetest):
                    continue

            # Processing current dir : compute dir size, and store file sizes into sizefiles
            dirsize=0
            for file in files:
                path = dir + "/" + file
                #path2=path.encode('utf-8', 'surrogateescape') # .decode('ISO-8859-1') 
                if not os.path.exists(path) or not os.access(path, os.R_OK) or not os.path.isfile(path):
                    # Skip broken symlinks, and cases where we do not have access rights. TODO: check whether access rights are tied to inode or path
                    #sys.stderr.write("Unable to access %s!\n" % (path,))
                    continue
                filestat = os.lstat(path)
                filesize = int(filestat.st_size)
                processedsize+=filesize
                processedfiles+=1
                dirsize += filesize
                xxh = xxhash_file(path, filesize)
                #bisect.insort(dircontents[dir], xxh)
                dircontents[dir].append(xxh)
                res = (
                    None,
                    dir,
                    file,
                    filesize,
                    xxh,
                    filestat.st_mtime, filestat.st_mode, filestat.st_uid, filestat.st_gid, filestat.st_ino, filestat.st_nlink, filestat.st_dev,
                    None
                )
                reslen= '(' + '?,' * (len(res)-1) + '?)'
                cur.execute('insert into files values ' + reslen, res)
                #sys.stderr.write("\033[2K\r%s\rScanning: [%d %%, %d MB, %d files] %s" % (" " * 500, 100*processedsize/totalsize/1024, processedsize>>20, processedfiles, path))
                #progress.updatef()

            # Increment all parents dir size with current dir size
            dirtmp=dir
            while(dirsize > 0 and dirtmp != init_path and dirtmp != '/'):
                dirsizes[dirtmp] += dirsize
                dirtmp = os.path.dirname(dirtmp)
            conn.commit()
            sys.stderr.write("\033[2K\rScanning: [%d %%, %d MB, %d files] %s" % (100*processedsize/totalsize/1024, processedsize>>20, processedfiles, dir))
            sys.stderr.flush()

        for (dir, dirs, files) in os.walk(init_path, topdown=False):
            # Compute "directory hash"
            foo = np.array(dircontents[dir], dtype=np.int64)
            foo.sort()
            dirxxh = xxhash.xxh64(foo.tobytes()).intdigest() - (1<<63)
            parentdir=os.path.dirname(dir)
            if (parentdir != '/'):
                dircontents[parentdir].append(dirxxh)
            #bisect.insort(dircontents[os.path.dirname(dir)], dirxxh)
            dirstat = os.lstat(dir)
            resdir = (
                    None,
                    parentdir,
                    os.path.basename(dir),
                    dirsizes[dir],
                    len(files), len(dirs),
                    dirxxh,
                    dirstat.st_mtime, dirstat.st_mode, dirstat.st_uid, dirstat.st_gid, dirstat.st_dev,
                    None
                )
            reslen2 =  '(' + '?,' * (len(resdir)-1) + '?)'
                
            cur.execute('insert into dirs values ' + reslen2, resdir)

if __name__ == "__main__":
    # execute only if run as a script
    dbname=sys.argv[1]
    basedir=sys.argv[2]
    #basesize=int(sys.argv[3])*1024
    basesize=6311500536*1024
    print((dbname,basedir,basesize))
    createdb(dbname)
    scandir(dbname, basedir, basesize)
    