set -e
set -x

archive_url="https://oleanstorage.azureedge.net/mathlib/"

new_git_sha=$(python scripts/look_up_olean_hash.py $lean_file_hash) || exit 0
echo "equivalent Git sha: $new_git_sha"
curl "$archive_url$new_git_sha.tar.gz" | tar xz src
