DEPLOY_NIGHTLY_GITHUB_USER=leanprover-community-bot

set -e
set -x

# By default, github actions overrides the credentials used to access any
# github url so that it uses the github-actions[bot] user.  We want to access
# github using a different username.
git config --unset http.https://github.com/.extraheader

git_hash="$(git log -1 --pretty=format:%h)"
git clone https://github.com/leanprover-community/doc-gen.git
cd doc-gen
sed -i "s/rev = \"\S*\"/rev = \"$git_hash\"/" leanpkg.toml
echo -e "builtin_path\npath ./src\npath ../src" > leanpkg.path
git clone "https://$DEPLOY_NIGHTLY_GITHUB_USER:$DEPLOY_NIGHTLY_GITHUB_TOKEN@github.com/leanprover-community/mathlib_docs.git"
rm -rf mathlib_docs/docs/
elan override set leanprover-community/lean:nightly
python3 -m pip install --upgrade pip
pip3 install markdown2 toml
./gen_docs -w -r "../" -t "mathlib_docs/docs/"
cd mathlib_docs/docs
git add -A .
git config user.name "leanprover-community-bot"
git config user.email "leanprover.community@gmail.com"
git commit -m "automatic update to $git_hash"
#--author="leanprover-community-bot <leanprover.community@gmail.com>"
git push
