#!/usr/bin/env python3
import os.path
import os
import sys
import tarfile
from git import Repo
from github import Github

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


def mathlib_asset(rev):
    global repo
    mathlib = [ 'https://github.com/leanprover/mathlib',
                'https://github.com/leanprover-community/mathlib',
                'https://www.github.com/leanprover/mathlib',
                'https://www.github.com/leanprover-community/mathlib']
    if not any([ r.url in mathlib for r in repo.remotes ]): return False

    g = Github()
    print("Querying GitHub...")
    repo = g.get_repo("leanprover-community/mathlib-nightly")
    tags = {tag.name: tag.commit.sha for tag in repo.get_tags()}
    try:
        release = next(r for r in repo.get_releases()
                           if r.tag_name.startswith('nightly-') and
                           tags[r.tag_name] == rev)
    except StopIteration:
        print('Error: no nightly archive found')
        return False

    try:
        asset = next(x for x in release.get_assets()
                     if x.name.startswith('mathlib-olean-nightly-'))
    except StopIteration:
        print("Error: Release " + release.tag_name + " does not contains a olean "
              "archive (this shouldn't happen...)")
        return False
    return asset

def fetch_mathlib(asset):
    mathlib_dir = os.path.join(os.environ['HOME'], '.mathlib')
    if not os.path.isdir(mathlib_dir):
        os.mkdir(mathlib_dir)

    if not os.path.isfile(os.path.join(mathlib_dir, asset.name)):
        print("Downloading nightly...")
        cd = os.getcwd()
        os.chdir(mathlib_dir)
        http = urllib3.PoolManager(
            cert_reqs='CERT_REQUIRED',
            ca_certs=certifi.where())
        req = http.request('GET', asset.browser_download_url)
        with open(asset.name, 'wb') as f:
            f.write(req.data)
        os.chdir(cd)
    else:
        print("Reusing cached olean archive")

    print("Extracting nightly...")
    ar = tarfile.open(os.path.join(mathlib_dir, asset.name))
    ar.extractall('.')
    return True

rev = repo.commit().hexsha
fn = os.path.join(cache_dir, 'olean-' + rev + ".bz2")

if __name__ == "__main__":
    if sys.argv[1:] == ['--fetch']:
        asset = mathlib_asset(rev)
        if asset:
            fetch_mathlib(asset)
        elif os.path.exists(fn):
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
