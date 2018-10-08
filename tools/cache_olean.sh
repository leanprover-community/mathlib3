#! /bin/sh
if [ "$1" = "" ]
then
    BRANCH=`git branch | awk '/\*/ { print $2; }'`
else
    BRANCH=$1
fi
echo caching .olean files of $BRANCH ...
BINARIES=`git ls-files | grep .lean | sed "s/\\.lean/.olean/"`
mkdir -p .bin/branches/$BRANCH
rsync -R -E $BINARIES .bin/branches/$BRANCH
