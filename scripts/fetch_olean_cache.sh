set -e
set -x

archive_url="https://oleanstorage.azureedge.net/mathlib/"

if [[ `wget -S --spider $archive_url$git_sha.tar.gz  2>&1 | grep 'HTTP/1.1 200 OK'` ]]; then
  curl "$archive_url$git_sha.tar.gz" | tar xz --wildcards *.olean
else
  new_git_sha=$(python scripts/look_up_olean_hash.py $lean_file_hash) || exit 0
  echo "new hash $new_git_sha"
  curl "$archive_url$new_git_sha.tar.gz" | tar xz --wildcards *.olean
fi
