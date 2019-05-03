#! /bin/sh
HOOK_DIR=`git rev-parse --git-dir`/hooks
if [ -e $HOOK_DIR ]; then
	echo This script will copy post-commit and post-checkout scripts to $HOOK_DIR
	read -p "Do you want to proceed? " -n 1 -r
	echo    # (optional) move to a new line
	if [[ $REPLY =~ ^[Yy]$ ]]
	then
	    cp $HOME/.mathlib/hooks/post-commit $HOOK_DIR &&
	    cp $HOME/.mathlib/hooks/post-checkout $HOOK_DIR &&
	    echo "Successfully copied scripts"
	else
		echo "Cancelled..."
	fi
else
    echo No git repo found
    exit -1
fi
