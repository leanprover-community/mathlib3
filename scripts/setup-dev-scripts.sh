#! /bin/sh
pip3 install toml PyGithub urllib3 certifi gitpython
BASEDIR=$(dirname "$0")
cd $BASEDIR
mkdir -p $HOME/.mathlib/bin || true
mkdir -p $HOME/.mathlib/hooks || true
cp update-mathlib.py $HOME/.mathlib/bin/update-mathlib
cp cache-olean.py $HOME/.mathlib/bin/cache-olean
cp setup-lean-git-hooks.sh $HOME/.mathlib/bin/setup-lean-git-hooks
cp post-commit $HOME/.mathlib/hooks/
cp post-checkout $HOME/.mathlib/hooks/
if [ "`which update-mathlib`" != "$HOME/.mathlib/bin/update-mathlib" ]; then
    echo adding "export PATH=\"\$HOME/.mathlib/bin:\$PATH\"" in \$HOME/.profile
    echo "export PATH=\"\$HOME/.mathlib/bin:\$PATH\" " >> $HOME/.profile
    echo Run: \"source \$HOME/.profile\"
else
    echo already in \$PATH
fi
