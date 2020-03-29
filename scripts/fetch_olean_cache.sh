set -e
set -x

archive_url="https://oleanstorage.azureedge.net/mathlib/"
MAX_REQUESTS=10

if new_git_sha=$(python scripts/look_up_olean_hash.py $lean_file_hash); then
  echo "equivalent Git sha: $new_git_sha"
else
  git log --skip=1 -$MAX_REQUESTS --first-parent --pretty=format:%H
  for new_git_sha in $(git log --skip=1 -$MAX_REQUESTS --first-parent --pretty=format:%H)
  do
    echo "$new_git_sha"
    if curl -fI "$archive_url$new_git_sha.tar.gz" ; then
      echo "found ancestor Git sha: $new_git_sha"
      break
    fi
    new_git_sha=""
  done
fi
# exit if there were no successful requests
[ "$new_git_sha" != "" ] || exit 0

curl "$archive_url$new_git_sha.tar.gz" | tar xz src
