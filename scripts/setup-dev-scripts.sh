#! /bin/sh
echo "Installing python dependencies (at user level)"
pip3 install --user toml PyGithub urllib3 certifi gitpython
echo "Installing mathlib scripts"
BASEDIR=$(dirname "$0")
cd $BASEDIR
mkdir -p $HOME/.mathlib/bin || true
mkdir -p $HOME/.mathlib/hooks || true
cp update-mathlib.py $HOME/.mathlib/bin/update-mathlib
cp cache-olean.py $HOME/.mathlib/bin/cache-olean
cp setup-lean-git-hooks.sh $HOME/.mathlib/bin/setup-lean-git-hooks
cp post-commit $HOME/.mathlib/hooks/
cp post-checkout $HOME/.mathlib/hooks/
if grep -q ".mathlib/bin" $HOME/.profile
then
    echo mathlib scripts are already added to \$PATH in .profile
else
    echo adding "export PATH=\"\$HOME/.mathlib/bin:\$PATH\"" in \$HOME/.profile
    echo "export PATH=\"\$HOME/.mathlib/bin:\$PATH\" " >> $HOME/.profile
    echo Run: \"source \$HOME/.profile\"
fi
