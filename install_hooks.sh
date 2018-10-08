#! /bin/sh
chmod +x post-commit pre-rebase post-checkout cache_olean.sh restore_olean.sh 
GITDIR=`git rev-parse --git-dir`
mkdir -p $GITDIR/hooks/
cp post-commit pre-rebase post-checkout cache_olean.sh restore_olean.sh $GITDIR/hooks/
