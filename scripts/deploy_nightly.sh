set -e				# fail on error

DEPLOY_NIGHTLY_GITHUB_USER=leanprover-community-bot
git remote add mathlib "https://$DEPLOY_NIGHTLY_GITHUB_USER:$DEPLOY_NIGHTLY_GITHUB_TOKEN@github.com/leanprover-community/mathlib.git"
git remote add nightly "https://$DEPLOY_NIGHTLY_GITHUB_USER:$DEPLOY_NIGHTLY_GITHUB_TOKEN@github.com/leanprover-community/mathlib-nightly.git"

# After this point, we don't use any secrets in commands.
set -x				# echo commands

# By default, github actions overrides the credentials used to access any
# github url so that it uses the github-actions[bot] user.  We want to access
# github using a different username.
git config --unset http.https://github.com/.extraheader

# The checkout action produces a shallow repository from which we cannot push.
git fetch --unshallow || true

git fetch nightly --tags

# Create a tag name based on the current date.
MATHLIB_VERSION_STRING="nightly-$(date -u +%F)"

# Check if the tag already exists. If so, exit (successfully).
# This way we create a release/update the lean-x.y.z branch
# only once per day.
if git rev-parse --verify -q $MATHLIB_VERSION_STRING; then
    exit 0
fi

if command -v greadlink >/dev/null 2>&1; then
    # macOS readlink doesn't support -f option
    READLINK=greadlink
else
    READLINK=readlink
fi

# Try to update the lean-x.y.z branch on mathlib. This could fail if
# a subsequent commit has already pushed an update.
LEAN_VERSION="lean-3.5.1"

git push mathlib HEAD:refs/heads/$LEAN_VERSION || \
    echo "mathlib rejected push to branch $LEAN_VERSION; maybe it already has a later version?" >&2

# Push the commits to a branch on nightly and push a tag.
git push nightly HEAD:"mathlib-master" || true
git tag $MATHLIB_VERSION_STRING
git push nightly tag $MATHLIB_VERSION_STRING

# Travis can't publish releases to other repos (or stop mucking with the markdown description), so push releases directly
export GOPATH=$($READLINK -f go)
PATH=$PATH:$GOPATH/bin
go get github.com/itchio/gothub

# Build olean and script tarballs.
OLEAN_ARCHIVE=mathlib-olean-$MATHLIB_VERSION_STRING.tar.gz
SCRIPT_ARCHIVE=mathlib-scripts-$MATHLIB_VERSION_STRING.tar.gz
git clone https://github.com/leanprover-community/mathlib-tools
tar czf $OLEAN_ARCHIVE src
rm -rf mathlib-scripts
cp -a mathlib-tools/scripts mathlib-scripts
tar czf $SCRIPT_ARCHIVE mathlib-scripts
ls *.tar.gz

# Create a release associated with the tag and upload the tarballs.
export GITHUB_TOKEN=$DEPLOY_NIGHTLY_GITHUB_TOKEN
gothub release -u leanprover-community -r mathlib-nightly -t $MATHLIB_VERSION_STRING -d "Mathlib's .olean files and scripts" --pre-release
gothub upload -u leanprover-community -r mathlib-nightly -t $MATHLIB_VERSION_STRING -n "$(basename $OLEAN_ARCHIVE)" -f "$OLEAN_ARCHIVE"
gothub upload -u leanprover-community -r mathlib-nightly -t $MATHLIB_VERSION_STRING -n "$(basename $SCRIPT_ARCHIVE)" -f "$SCRIPT_ARCHIVE"
