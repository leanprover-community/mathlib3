DEPLOY_NIGHTLY_GITHUB_USER=leanprover-community-bot

set -e
set -x

cd scripts
./mk_all.sh
lean --run mk_nolint.lean
./rm_all.sh

git remote add origin-bot "https://$DEPLOY_NIGHTLY_GITHUB_USER:$DEPLOY_NIGHTLY_GITHUB_TOKEN@github.com/leanprover-community/mathlib.git"
git config user.email "leanprover.community@gmail.com"
git config user.name "leanprover-community-bot"
git add nolints.txt
git commit -m "chore(scripts): update nolints.txt" || true
git push origin-bot HEAD:master || true
