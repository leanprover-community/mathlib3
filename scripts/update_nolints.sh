DEPLOY_NIGHTLY_GITHUB_USER=leanprover-community-bot

set -e
set -x

git add scripts/nolints.txt
git commit -m "chore(scripts): update nolints.txt" || true
git push origin-bot HEAD:master || true
