set -e
set -x

archive_url="https://oleanstorage.azureedge.net/mathlib/"

# GIT_HISTORY_DEPTH is set in .github/workflows/build.yml
for new_git_sha in $(git log -$GIT_HISTORY_DEPTH --first-parent --pretty=format:%H)
do
  if curl -sfI "$archive_url$new_git_sha.tar.xz" ; then
    echo "found ancestor Git sha: $new_git_sha"
    break
  fi
  new_git_sha=""
done
# exit if there were no successful requests
[ "$new_git_sha" != "" ] || exit 0

# A list of directories containing .olean files. We are being conservative to
# avoid traversing irrelevant directories and affecting directories we do not
# want changed (e.g. $root/.git).
dirs="src"

# if there are errors extracting the olean cache, delete all oleans and continue
(curl "$archive_url$new_git_sha.tar.xz" | tar xJ src) || {
find $dirs -name "*.olean" -delete || true
}

# Delete every <path>.olean where <path>.lean appears in "src/.noisy_files"
if [ -e $dirs/.noisy_files ]; then
  sed 's/\.lean$/.olean/' $dirs/.noisy_files | xargs -d'\n' rm -f
  rm $dirs/.noisy_files
fi

# Archives no longer contain .lean files, but they used to.
# Extracting such an archive overwrites all .lean files, which is fine if we
# downloaded an "equivalent" cache. However, since we might be using an older
# cache, we must revert any changes made to the .lean files.
#
# The following commands don't make any changes to ignored files, so the .olean
# files should be OK.
git reset --hard HEAD
git clean -f -d

# Delete every <path>.olean without a matching <path>.lean.
# n.b. this for loop will break if there are filenames with spaces
for olean_file in `find $dirs -name "*.olean"`
do
  lean_file=${olean_file/%.olean/.lean}
  if [ ! -e $lean_file ]; then
    rm $olean_file
  fi
done

# Delete all empty directories. An empty directory may have been created if it
# does not contain any .lean files and all of its .olean files were deleted.
find $dirs -type d -empty -delete
