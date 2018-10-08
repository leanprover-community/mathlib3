#! /bin/sh
chmod +x post-commit pre-rebase post-checkout cache_olean.sh restore_olean.sh 
mkdir -p .git/hooks/
cp post-commit pre-rebase post-checkout cache_olean.sh restore_olean.sh .git/hooks/
