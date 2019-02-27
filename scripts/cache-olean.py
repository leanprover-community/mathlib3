#!/usr/bin/env python3
import os.path
import os
import sys
import tarfile
from git import Repo

def make_cache():
    global fn
    if os.path.exists(fn):
        os.remove(fn)

    ar = tarfile.open(fn, 'w|bz2')
    if os.path.exists('src/'): ar.add('src/')
    if os.path.exists('test/'): ar.add('test/')
    ar.close()

while not os.path.isdir('.git') and not os.getcwd() == '/':
    os.chdir(os.path.dirname(os.getcwd()))
if not os.path.isdir('.git'):
    raise('no .git repo')
root_dir = os.getcwd()
cache_dir = os.path.join(root_dir, "_cache")

repo = Repo(os.getcwd())
if repo.bare:
    print('repo not initialized')
    sys.exit(-1)

if not os.path.exists(cache_dir):
    os.makedirs(cache_dir)

fn = os.path.join(cache_dir, 'olean-' + repo.commit().hexsha + ".bz2")

if sys.argv[1:] == ['--fetch']:
    if os.path.exists(fn):
        ar = tarfile.open(fn, 'r')
        ar.extractall(root_dir)
        ar.close()
    else:
        print('no cache found')
elif sys.argv[1:] == ['--build']:
    if os.system('leanpkg build') == 0:
        make_cache()
elif sys.argv[1:] == []:
    make_cache()
else:
    print('usage: cache_olean.py [--fetch | --build]')
