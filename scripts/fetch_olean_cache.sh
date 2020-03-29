set -e
set -x

archive_url="https://oleanstorage.azureedge.net/mathlib/"

if new_git_sha=$(python scripts/look_up_olean_hash.py $lean_file_hash); then
  echo "equivalent Git sha: $new_git_sha"
else
  # GIT_HISTORY_DEPTH is set in .github/workflows/build.yml
  for new_git_sha in $(git log -$GIT_HISTORY_DEPTH --first-parent --pretty=format:%H)
  do
    if curl -sfI "$archive_url$new_git_sha.tar.gz" ; then
      echo "found ancestor Git sha: $new_git_sha"
      break
    fi
    new_git_sha=""
  done
fi
# exit if there were no successful requests
[ "$new_git_sha" != "" ] || exit 0

curl "$archive_url$new_git_sha.tar.gz" | tar xz src

# extracting the archive overwrites all .lean files, which is fine if we
# downloaded an "equivalent" cache. However, since we might be using an older
# cache, we must revert any changes to the .lean files
git reset --hard HEAD

# A list of directories containing .olean files. We are being conservative to
# avoid traversing irrelevant directories and affecting directories we do not
# want changed (e.g. $root/.git).
dirs="src"

# Delete every <path>.olean without a matching <path>.lean.

for olean_file in `find $dirs -name "*.olean"`
do
    lean_file=${olean_file/%.olean/.lean}
    if [ ! -e $lean_file ]; then
        echo "rm $olean_file"
        rm $olean_file
    fi
done

# Delete all empty directories. An empty directory may have been created if it
# does not contain any .lean files and all of its .olean files were deleted.

find $dirs -type d -empty -delete
