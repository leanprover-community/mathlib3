#! /bin/sh
pip3 install toml PyGithub urllib3 certifi
mkdir -p $HOME/.mathlib/bin || true
cp update-mathlib.py $HOME/.mathlib/bin/update-mathlib
echo "export PATH=\"\$HOME/.mathlib/bin:\$PATH\" " >> $HOME/.profile
source $HOME/.profile
