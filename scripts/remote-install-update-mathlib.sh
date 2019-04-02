#! /bin/sh
echo "Installing python dependencies (at user level)"
pip3 install --user toml PyGithub urllib3 certifi GitPython
echo "Fetching the update-mathlib script"
curl -o update-mathlib.py https://raw.githubusercontent.com/leanprover-community/mathlib/master/scripts/update-mathlib.py
echo "installing it in \$HOME/.mathlib/bin"
chmod +x update-mathlib.py
mkdir -p $HOME/.mathlib/bin || true
mv update-mathlib.py $HOME/.mathlib/bin/update-mathlib
if grep -q ".mathlib/bin" $HOME/.profile
then
    echo mathlib scripts are already added to \$PATH in .profile
else
	echo "Adding a path modification in .profile"
    echo "export PATH=\"\$HOME/.mathlib/bin:\$PATH\" " >> $HOME/.profile
	echo "You should now run \"source $HOME/.profile\""
fi
