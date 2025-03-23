#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Aug 24 01:48:57 2024

@author: adrien
"""

import sqlite3
import string
delchars = string.punctuation + ' '   #delchars = ''.join(c for c in map(chr, range(256)) if not c.isalnum())
tab = str.maketrans(delchars, delchars, delchars)
def get_ext_len(x):
    if not '.' in x: return None
    l = x.rindex('.')+1
    if l==1: return None  # case for ".bashrc", etc.
    ext = x[l:]
    if len(ext)>16: return None
    if ext!=ext.translate(tab): return None
    return l+1

def migrate3(dbname, version_orig=2, version_target=3):
    conn = sqlite3.connect(dbname)
    #conn.create_function("get_ext_len", 1, lambda x: None if not '.' in x or len(x)-x.rindex('.')+2 > 16 else x.rindex('.')+2)
    conn.create_function("get_ext_len", 1, get_ext_len)
    cur = conn.cursor()

    if version_orig==2:
        cur.executescript('''alter table entries add ext_len integer;
                             alter table entries add extension text GENERATED ALWAYS AS (lower(substr(path,ext_len))) VIRTUAL;
                             create index entries_ext_idx on entries(extension);
                             update entries set ext_len=get_ext_len(path) where type='F';
                          ''')
        print("OK")

def migrate2(dbname):
    conn = sqlite3.connect(dbname)
    cur = conn.cursor()
    print("Migrating DB")  # FIXME: nsbubfiles_rec is not processed yet
    self.cur.executescript('''
            drop index entries_name_idx;
            alter table entries drop column name;
            update entries set parentdir_len=1 where parentdir_len=0 and path!='/';
            alter table entries add column name text GENERATED ALWAYS AS (substr(path,parentdir_len+iif(parentdir_len<2,1,2))) VIRTUAL;
            create index entries_name_idx on entries(name);
        ''')

def migrate(dbname):
    """Migrate from old to new DB schema (table 'entries' instead of tables 'files', 'dirs' and 'symlinks')"""
    conn = sqlite3.connect(dbname)
    cur = conn.cursor()
    tables = [k[0] for k in self.cur.execute("select name from sqlite_master where type='table'").fetchall()]
    populate_nsubfiles_rec=False
    if 'files' in tables and 'dirs' in tables and not 'entries' in tables:
        print("Migrating DB")  # FIXME: nsbubfiles_rec is not processed yet
        self.cur.executescript('''
            drop table if exists entries;
            create table entries(
                id integer primary key autoincrement,
                type CHAR(1) NOT NULL,
                path text UNIQUE NOT NULL,
                parentdir_len integer,
                parentdir text GENERATED ALWAYS AS (substr(path,1,parentdir_len)) VIRTUAL,
                name text GENERATED ALWAYS AS (substr(path,parentdir_len+iif(parentdir_len<2,1,2))) VIRTUAL,
                size integer,
                hash integer,
                magictype integer,
                nsubdirs integer,
                nsubfiles integer,
                nsubfiles_rec integer,
                symtarget text,
                st_mtime integer, st_mode integer, st_uid integer, st_gid integer, st_ino integer, st_nlink integer, st_dev integer,
                dbsession integer not null
            );
            create index entries_parentdir_idx on entries(parentdir);
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
        populate_nsubfiles_rec = True
    else:
        sql = self.cur.execute("select sql from sqlite_master where type='table' and name='entries'").fetchall()[0]
        if not 'nsubfiles_rec integer' in sql:
            print("Adding column nsubfiles_rec")
            self.cur.execute("alter table entries add nsubfiles_rec integer")
            populate_nsubfiles_rec = True

    if populate_nsubfiles_rec:
        print("Generating nsubfiles_rec")
        rs = self.cur.execute("select path,nsubfiles,nsubdirs from entries where type='D' and not path in ('','/')")
        for path,nsubfiles,nsubdirs in rs:
            if nsubdirs>0:
                nsubfiles_r = self.nsubfiles_rec(path)
        self.cur.execute("update entries set nsubfiles_rec=nsubfiles where nsubdirs=0 and type='D'")
    self.conn.commit()

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("dbfile", help="DB path")
    newdb = "new_" + dbfile
    shutil.copyfile(args.dbfile, newdb)
    migrate(newdb)
