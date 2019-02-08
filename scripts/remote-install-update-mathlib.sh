#! /bin/sh
pip3 install toml PyGithub urllib3 certifi
curl -o update-mathlib.py https://raw.githubusercontent.com/leanprover-community/mathlib/master/scripts/update-mathlib.py
chmod +x update-mathlib.py
mv update-mathlib.py /usr/local/bin/update-mathlib
