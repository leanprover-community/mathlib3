DEPLOY_NIGHTLY_GITHUB_USER=leanprover-community-bot

set -e
set -x

# By default, github actions overrides the credentials used to access any
# github url so that it uses the github-actions[bot] user.  We want to access
# github using a different username.
git config --unset http.https://github.com/.extraheader

cd scripts
./mk_all.sh
lean --run mk_nolint.lean
./rm_all.sh

git remote add origin-bot "https://$DEPLOY_NIGHTLY_GITHUB_USER:$DEPLOY_NIGHTLY_GITHUB_TOKEN@github.com/robertylewis/mathlib.git"
git config user.email "leanprover.community@gmail.com"
git config user.name "leanprover-community-bot"
git add nolints.txt
git commit -m "chore(scripts): update nolints.txt"
git push origin-bot HEAD:master
