#! /bin/sh
PYTHON_DEPS="toml PyGithub urllib3 certifi gitpython"

USER="--user"
USER_MSG="(at user level)"
if [[ $1 = "--global" ]]; then
    USER=""
    USER_MSG="(globally)"
fi
which apt-get > /dev/null
USE_APT_GET=$?
CMD_INSTALL="pip3 install $USER"
PKG_CHECK="pip3 show"
if $USE_APT_GET; then
    CMD_INSTALL="sudo apt-get install"
    OLD_PYTHON_DEPS=$PYTHON_DEPS
    PYTHON_DEPS=
    for dep in $PYTHON_DEPS; do
        PYTHON_DEPS=$PYTHON_DEPS python3-$dep
    done
    PKG_CHECK="apt-cache policy"
elif ! which pip3 > /dev/null; then
    if which brew; then
        read -p "update-mathlib needs to install python3 and pip3. Proceed?" -n 1 -r
        echo
        if [[ $REPLY =~ ^[Yy]$ ]]; then
            brew install python3
        else
            exit -1
        fi
    elif which choco; then
        read -p "update-mathlib needs to install python3 and pip3. Proceed?" -n 1 -r
        echo
        if [[ $REPLY =~ ^[Yy]$ ]]; then
            choco install python
        else
            exit -1
        fi
    else
        echo "python3 and pip3 not found. First install python3 and pip3 and then install update-mathlib"
        exit -1
    fi
fi

PYTHON_DEPS_AVAILABLE=0
for dep in $PYTHON_DEPS ; do
	if ! $PKG_CHECK $dep > /dev/null ; then
		PYTHON_DEPS_AVAILABLE=1
	fi
done

touch $HOME/.profile
X=$(grep -q ".mathlib/bin" $HOME/.profile)
SCRIPTS_ON_PATH=$?

echo "This script will:"
if [[ $PYTHON_DEPS_AVAILABLE -ne 0 ]]; then
	echo "* use '$CMD_INSTALL' to install required python dependencies"
fi
echo "* copy the mathlib dev scripts to ~/.mathlib/bin"
echo "* copy the mathlib git hooks to ~/.mathlib/hooks"
echo "   (but you'll still need to run 'setup-lean-git-hooks' in each repository to install these)"
if [[ $SCRIPTS_ON_PATH -ne 0 ]]; then
	echo "* add ~/.mathlib/bin to the PATH in your '.profile' file"
fi
echo
read -p "Do you want to proceed? " -n 1 -r
echo
if [[ $REPLY =~ ^[Yy]$ ]]
then
	if [[ $PYTHON_DEPS_AVAILABLE -ne 0 ]]; then
		echo "... Installing python dependencies $USER_MSG"
		$CMD_INSTALL $PYTHON_DEPS
	else
		echo "... Python dependencies already available"
	fi
	echo "... Installing mathlib scripts"
	# TODO we could test the status of all these files, and skip this step if everything is already up to date?
	BASEDIR=$(dirname "$0")
	cd $BASEDIR
	mkdir -p $HOME/.mathlib/bin || true
	mkdir -p $HOME/.mathlib/hooks || true
	cp auth_github.py          $HOME/.mathlib/bin/
	cp delayed_interrupt.py    $HOME/.mathlib/bin/
	cp update-mathlib.py       $HOME/.mathlib/bin/update-mathlib
	cp cache-olean.py          $HOME/.mathlib/bin/cache-olean
	cp setup-lean-git-hooks.sh $HOME/.mathlib/bin/setup-lean-git-hooks
        chmod +x $HOME/.mathlib/bin/update-mathlib
        chmod +x $HOME/.mathlib/bin/cache-olean
        chmod +x $HOME/.mathlib/bin/setup-lean-git-hooks
	cp post-commit   $HOME/.mathlib/hooks/
	cp post-checkout $HOME/.mathlib/hooks/
	if [[ $SCRIPTS_ON_PATH -eq 0 ]]
	then
	    echo ... mathlib scripts are already added to \$PATH in .profile
	else
	    echo ... adding "export PATH=\"\$HOME/.mathlib/bin:\$PATH\"" in \$HOME/.profile
	    echo "export PATH=\"\$HOME/.mathlib/bin:\$PATH\" " >> $HOME/.profile
	    echo ... now run: \"source \$HOME/.profile\"
	fi
	echo "... finished setting up development scripts."
else
	echo "Cancelled..."
fi
