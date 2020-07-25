set -ex

# The checkout action produces a shallow repository from which we cannot push.
git fetch --unshallow || true

# Try to update the lean-x.y.z branch on mathlib. This could fail if
# a subsequent commit has already pushed an update.
# short_lean_version is of the form 3.5.1, set earlier in CI
LEAN_VERSION="lean-$short_lean_version"

git push origin-bot HEAD:refs/heads/$LEAN_VERSION || \
    echo "mathlib rejected push to branch $LEAN_VERSION; maybe it already has a later version?" >&2
