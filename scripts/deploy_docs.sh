DEPLOY_GITHUB_USER=leanprover-community-bot

set -e
set -x

lean_version="$(sed '/^lean_version/!d;s/.*"\(.*\)".*/\1/' leanpkg.toml)"

git_hash="$(git log -1 --pretty=format:%h)"
git clone https://github.com/leanprover-community/doc-gen.git
cd doc-gen

# the commit hash in leanpkg.toml is used by doc_gen.
sed -i "s/rev = \"\S*\"/rev = \"$git_hash\"/" leanpkg.toml

echo -e "builtin_path\npath ./src\npath ../src" > leanpkg.path
git clone "https://$DEPLOY_GITHUB_USER:$DEPLOY_GITHUB_TOKEN@github.com/leanprover-community/mathlib_docs.git"

# skip if docs for this commit have already been generated
if [ "$(cd mathlib_docs && git log -1 --pretty=format:%s)" == "automatic update to $git_hash" ]; then
  exit 0
fi

rm -rf mathlib_docs/docs/

# Force doc_gen project to match the Lean version used in CI.
# If they are incompatible, something in doc_gen will fail to compile,
# but this is better than trying to recompile all of mathlib.
elan override set "$lean_version"

python3 -m pip install --upgrade pip
pip3 install markdown2 toml
./gen_docs -w -r "../" -t "mathlib_docs/docs/"

if [ "$github_repo" = "leanprover-community/mathlib" -a "$github_event" = "push" -a "$github_ref" = "refs/heads/master" ]; then
  cd mathlib_docs/docs
  git config user.email "leanprover.community@gmail.com"
  git config user.name "leanprover-community-bot"
  git add -A .
  git checkout --orphan master2
  git commit -m "automatic update to $git_hash"
  git push -f origin HEAD:master
fi
