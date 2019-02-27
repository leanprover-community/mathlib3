#! /bin/sh
if [ -e .git/hooks/ ]; then
    cp $HOME/.mathlib/hooks/post-commit .git/hooks/
    cp $HOME/.mathlib/hooks/post-checkout .git/hooks/
else
    echo No git repo found
    exit -1
fi
