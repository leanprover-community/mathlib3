#! /bin/sh
pip3 install toml PyGithub urllib3 certifi
mkdir $HOME/.mathlib/bin || true
cp update-mathlib.py $HOME/.mathlib/bin/update-mathlib
echo "export PATH=\"\$HOME/.mathlib/bin:\$PATH\" " >> .profile
