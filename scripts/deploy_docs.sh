DEPLOY_NIGHTLY_GITHUB_USER=leanprover-community-bot

set -e
set -x

git_hash="$(git log -1 --pretty=format:%h)"
git clone https://github.com/leanprover-community/doc-gen.git
cd doc-gen
sed -i "s/rev = \"\S*\"/rev = \"$git_hash\"/" leanpkg.toml
echo -e "builtin_path\npath ./src\npath ../src" > leanpkg.path
git clone "https://$DEPLOY_NIGHTLY_GITHUB_USER:$DEPLOY_NIGHTLY_GITHUB_TOKEN@github.com/leanprover-community/mathlib_docs.git"
rm -rf mathlib_docs/docs/
elan override set leanprover-community/lean:3.5.1
python3 -m pip install --upgrade pip
pip3 install markdown2 toml
./gen_docs -w -r "../" -t "mathlib_docs/docs/"
cd mathlib_docs/docs
git config user.email "leanprover.community@gmail.com"
git config user.name "leanprover-community-bot"
git add -A .
git commit -m "automatic update to $git_hash"
git push
