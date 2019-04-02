#! /bin/sh
echo "This script will:"
echo "1. use 'pip3 install --user' to install required python dependencies"
echo "2. copy the mathlib dev scripts to ~/.mathlib/bin"
echo "3. copy the mathlib git hooks to ~/.mathlib/hooks"
echo "   (but you'll still need to run 'setup-lean-git-hooks' in each repository to install these)"
echo "4. add ~/.mathlib/bin to the PATH in your '.profile' file, if it is not already there."
echo
read -p "Do you want to proceed? " -n 1 -r
echo    # (optional) move to a new line
if [[ $REPLY =~ ^[Yy]$ ]]
then
	echo "Installing python dependencies (at user level)"
	pip3 install --user toml PyGithub urllib3 certifi gitpython
	echo "Installing mathlib scripts"
	BASEDIR=$(dirname "$0")
	cd $BASEDIR
	mkdir -p $HOME/.mathlib/bin || true
	mkdir -p $HOME/.mathlib/hooks || true
	cp auth_github.py          $HOME/.mathlib/bin/
	cp delayed_interrupt.py    $HOME/.mathlib/bin/
	cp update-mathlib.py       $HOME/.mathlib/bin/update-mathlib
	cp cache-olean.py          $HOME/.mathlib/bin/cache-olean
	cp setup-lean-git-hooks.sh $HOME/.mathlib/bin/setup-lean-git-hooks
	cp post-commit   $HOME/.mathlib/hooks/
	cp post-checkout $HOME/.mathlib/hooks/
	if grep -q ".mathlib/bin" $HOME/.profile
	then
	    echo mathlib scripts are already added to \$PATH in .profile
	else
	    echo adding "export PATH=\"\$HOME/.mathlib/bin:\$PATH\"" in \$HOME/.profile
	    echo "export PATH=\"\$HOME/.mathlib/bin:\$PATH\" " >> $HOME/.profile
	    echo Run: \"source \$HOME/.profile\"
	fi
else
	echo "Cancelled..."
fi

