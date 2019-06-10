set -e				# fail on error

# Only run on builds for pushes to the master branch.
if ! [ "$TRAVIS_EVENT_TYPE" = "push" -a "$TRAVIS_BRANCH" = "master" ]; then
    exit 0
fi

# Make sure we have access to secure Travis environment variables.
if ! [ "$TRAVIS_SECURE_ENV_VARS" = "true" ]; then
    echo 'deploy_nightly.sh: Build is a push to master, but no secure env vars.' >&2
    exit 1			# Something's wrong.
fi

git remote add mathlib "https://$GITHUB_TOKEN@github.com/leanprover-community/mathlib.git"
git remote add nightly "https://$GITHUB_TOKEN@github.com/leanprover-community/mathlib-nightly.git"

# After this point, we don't use any secrets in commands.
set -x				# echo commands

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
git push mathlib HEAD:$LEAN_VERSION || \
    echo "mathlib rejected push to branch $LEAN_VERSION; maybe it already has a later version?" >&2

# Push the commits to a branch on nightly and push a tag.
git push nightly HEAD:"mathlib-$TRAVIS_BRANCH" || true
git tag $MATHLIB_VERSION_STRING
git push nightly tag $MATHLIB_VERSION_STRING

# Travis can't publish releases to other repos (or stop mucking with the markdown description), so push releases directly
export GOPATH=$($READLINK -f go)
PATH=$PATH:$GOPATH/bin
go get github.com/itchio/gothub

# Build olean and script tarballs.
OLEAN_ARCHIVE=mathlib-olean-$MATHLIB_VERSION_STRING.tar.gz
SCRIPT_ARCHIVE=mathlib-scripts-$MATHLIB_VERSION_STRING.tar.gz
tar czf $OLEAN_ARCHIVE src
rm -rf mathlib-scripts
cp -a scripts mathlib-scripts
tar czf $SCRIPT_ARCHIVE mathlib-scripts
ls *.tar.gz

# Create a release associated with the tag and upload the tarballs.
gothub release -u leanprover-community -r mathlib-nightly -t $MATHLIB_VERSION_STRING -d "Mathlib's .olean files and scripts" --pre-release
gothub upload -u leanprover-community -r mathlib-nightly -t $MATHLIB_VERSION_STRING -n "$(basename $OLEAN_ARCHIVE)" -f "$OLEAN_ARCHIVE"
gothub upload -u leanprover-community -r mathlib-nightly -t $MATHLIB_VERSION_STRING -n "$(basename $SCRIPT_ARCHIVE)" -f "$SCRIPT_ARCHIVE"
