#! /bin/sh
pip3 install toml PyGithub urllib3 certifi
curl -o update-mathlib.py https://raw.githubusercontent.com/leanprover-community/mathlib/master/scripts/update-mathlib.py
chmod +x update-mathlib.py
mkdir -p $HOME/.mathlib/bin || true
cp update-mathlib.py $HOME/.mathlib/bin/update-mathlib
echo "export PATH=\"\$HOME/.mathlib/bin:\$PATH\" " >> $HOME/.profile
source $HOME/.profile
