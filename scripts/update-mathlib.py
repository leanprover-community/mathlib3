#!/usr/bin/env python3

from github import Github
import toml
import urllib3
import certifi
import os.path
import os
import tarfile


# find root of project and leanpkg.toml
cwd = os.getcwd()
while not os.path.isfile('leanpkg.toml') and not os.getcwd() == '/':
    os.chdir(os.path.dirname(os.getcwd()))
if not os.path.isfile('leanpkg.toml'):
    raise('no leanpkg.toml found')

mathlib_dir = os.path.join( os.environ['HOME'], '.mathlib' )
if not os.path.isdir(mathlib_dir):
    os.mkdir(mathlib_dir)

# parse leanpkg.toml
leanpkg = toml.load('leanpkg.toml')

if ( 'dependencies' in leanpkg and
     'mathlib' in leanpkg['dependencies'] ):
    lib = leanpkg['dependencies']['mathlib']

    # download archive
    if lib['git'] in ['https://github.com/leanprover/mathlib','https://github.com/leanprover-community/mathlib']:
        rev = lib['rev']
        hash = rev[:7]

        g = Github()
        repo = g.get_repo("leanprover-community/mathlib-nightly")
        assets = (r.get_assets() for r in (repo.get_releases())
                      if r.tag_name.startswith('nightly-') and
                      r.target_commitish == rev )
        assets = next(assets,None)
        if assets:
            a = next(x for x in assets if x.name.startswith('mathlib-olean-nightly-'))
            cd = os.getcwd()
            os.chdir(mathlib_dir)
            if not os.path.isfile(a.name):
                http = urllib3.PoolManager(
                    cert_reqs='CERT_REQUIRED',
                    ca_certs=certifi.where())
                r = http.request('GET', a.browser_download_url)
                f = open(a.name,'wb')
                f.write(r.data)
                f.close()
                os.chdir(cd)

                # extract archive
                ar = tarfile.open(os.path.join(mathlib_dir, a.name))
                ar.extractall('_target/deps/mathlib')
            else:
                print('no olean archive available')
else:
    print('project does not depend on mathlib')
