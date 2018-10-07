#! /bin/sh
if [ "$1" = "" ]
then
    BRANCH=`git branch | awk '/\*/ { print $2; }'`
else
    BRANCH=$1
fi
echo restoring .olean files of $BRANCH ...
BIN_CACHE=.bin/branches/$BRANCH
ROOT=`pwd`
if [ -e $BIN_CACHE ]
then
    cd $BIN_CACHE
    cp -a -R . $ROOT/
fi
