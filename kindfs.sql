PRAGMA user_version = 3;
drop table if exists entries;
create table entries(
    id integer primary key,
    type text NOT NULL,
    path text UNIQUE NOT NULL,
    parentdir_len integer,
    parentdir text GENERATED ALWAYS AS (substr(path,1,parentdir_len)) VIRTUAL,
    name text GENERATED ALWAYS AS (substr(path,parentdir_len+iif(parentdir_len<2,1,2))) VIRTUAL,
    ext_len integer,
    extension text GENERATED ALWAYS AS (substr(path,ext_len+iif(parentdir_len<2,1,2))) VIRTUAL,
    depht integer GENERATED ALWAYS AS (length(path)-length(replace(path,'/',''))-1) VIRTUAL,
    size integer,
    hash integer,
    magictype integer,
    nsubdirs integer,
    nsubfiles integer,
    nsubfiles_rec integer,
    symtarget text,
    st_mtime integer, st_mode integer, st_uid integer, st_gid integer, st_ino integer, st_nlink integer, st_dev integer,
    dbsession integer not null
) strict;
--create index entries_parentdir_idx on entries(parentdir);
--create index entries_path_idx on entries(path);
--create index entries_name_idx on entries(name);
--create index entries_ext_idx on entries(extension);
--create index entries_size_idx on entries(size);
--create index entries_hash_idx on entries(hash);
--create index entries_depht_idx on entries(depht);

--drop view if exists files;
--create view files as select id,parentdir,name,path,size,hash as xxh64be,st_mtime, st_mode, st_uid, st_gid, st_ino, st_nlink, st_dev,dbsession,magictype from entries where type='F';
--drop view if exists dirs;
--create view dirs as select id,parentdir,name,path,size,nsubfiles,nsubdirs,hash as xxh64be,st_mtime, st_mode, st_uid, st_gid, st_nlink, st_dev,dbsession,magictype from entries where type='D';
--drop view if exists symlinks;
--create view symlinks as select id,parentdir,name,path,symtarget as target,NULL as type,hash as xxh64be,dbsession,magictype from entries where type='S';

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

PRAGMA main.journal_mode=WAL;
--PRAGMA mmap_size = 268435456;
--PRAGMA main.page_size=4096;
PRAGMA cache_size = -50000;
PRAGMA locking_mode = EXCLUSIVE;
PRAGMA synchronous = NORMAL;
PRAGMA temp_store = MEMORY;
PRAGMA journal_mode = MEMORY;
PRAGMA foreign_keys = OFF;
PRAGMA auto_vacuum = NONE;
