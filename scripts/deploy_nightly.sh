
git remote add mathlib "https://$GITHUB_TOKEN@github.com/leanprover-community/mathlib.git"
git remote add nightly "https://$GITHUB_TOKEN@github.com/leanprover-community/mathlib-nightly.git"
git fetch nightly --tags

export MATHLIB_VERSION_STRING="nightly-$(date -u +%F)"

if command -v greadlink >/dev/null 2>&1; then
    # macOS readlink doesn't support -f option
    READLINK=greadlink
else
    READLINK=readlink
fi

# Travis can't publish releases to other repos (or stop mucking with the markdown description), so push releases directly
export GOPATH=$($READLINK -f go)
PATH=$PATH:$GOPATH/bin
go get github.com/itchio/gothub

HEAD=`git rev-parse --abbrev-ref HEAD`
if [ $HEAD = "master" ] && git tag $MATHLIB_VERSION_STRING
then
    last_tag=$(git describe @^ --abbrev=0 --tags)
    export OLEAN_ARCHIVE=mathlib-olean-$MATHLIB_VERSION_STRING.tar.gz
    export SCRIPT_ARCHIVE=mathlib-scripts-$MATHLIB_VERSION_STRING.tar.gz
    tar -zcvf $OLEAN_ARCHIVE src > /dev/null
    mkdir mathlib-scripts || true
    cp scripts/* mathlib-scripts/
    tar -zcvf $SCRIPT_ARCHIVE mathlib-scripts > /dev/null
    ls *.tar.gz
    gothub release -s $GITHUB_TOKEN -u leanprover-community -r mathlib-nightly -t $MATHLIB_VERSION_STRING -d "some description" --pre-release
    gothub upload -s $GITHUB_TOKEN -u leanprover-community -r mathlib-nightly -t $MATHLIB_VERSION_STRING -n "$(basename $OLEAN_ARCHIVE)" -f "$OLEAN_ARCHIVE"
    gothub upload -s $GITHUB_TOKEN -u leanprover-community -r mathlib-nightly -t $MATHLIB_VERSION_STRING -n "$(basename $SCRIPT_ARCHIVE)" -f "$SCRIPT_ARCHIVE"

    LEAN_VERSION=`python3 lean_version.py`
    git tag $LEAN_VERSION -f
    git push mathlib -f $LEAN_VERSION
fi
