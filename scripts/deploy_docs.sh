# Arguments:
# $1 : path to mathlib from working directory (mathlib: ".", doc-gen: "mathlib")
# $2 : path to doc-gen from mathlib (mathlib: "doc-gen", doc-gen: "..")
# $3 : path to mathlib from doc-gen (mathlib: "..", doc-gen: "mathlib")

DEPLOY_GITHUB_USER=leanprover-community-bot

set -e
set -x

cd $1
lean_version="$(sed '/^lean_version/!d;s/.*"\(.*\)".*/\1/' leanpkg.toml)"
mathlib_git_hash="$(git log -1 --pretty=format:%h)"

cd $2
docgen_git_hash="$(git log -1 --pretty=format:%h)"
# use the commit hash in mathlib's leanpkg.toml in doc_gen's leanpkg.toml
sed -i "s/rev = \"\S*\"/rev = \"$mathlib_git_hash\"/" leanpkg.toml
echo -e "builtin_path\npath ./src\npath $3/src" > leanpkg.path

git clone "https://$DEPLOY_GITHUB_USER:$DEPLOY_GITHUB_TOKEN@github.com/leanprover-community/mathlib_docs.git"

# skip if docs for this commit have already been generated
if [ "$(cd mathlib_docs && git log -1 --pretty=format:%s)" == "automatic update to mathlib $mathlib_git_hash using doc-gen $docgen_git_hash" ]; then
  exit 0
fi

rm -rf mathlib_docs/docs/

# Force doc_gen project to match the Lean version used in CI.
# If they are incompatible, something in doc_gen will fail to compile,
# but this is better than trying to recompile all of mathlib.
elan override set "$lean_version"

./gen_docs -w -r "$3/" -t "mathlib_docs/docs/"

if { [ "$github_repo" = "leanprover-community/mathlib" ] || [ "$github_repo" = "leanprover-community/doc-gen" ]; } && [ "$github_event" = "push" ] && [ "$github_ref" = "refs/heads/master" ]; then
  cd mathlib_docs/docs
  git config user.email "leanprover.community@gmail.com"
  git config user.name "leanprover-community-bot"
  git add -A .
  git checkout --orphan master2
  git commit -m "automatic update to mathlib $mathlib_git_hash using doc-gen $docgen_git_hash"
  git push -f origin HEAD:master
fi
