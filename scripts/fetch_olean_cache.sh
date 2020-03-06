set -e
set -x

if leanproject get-cache; then
  sleep 0
else
  new_olean_hash=$(python scripts/look_up_olean_hash.py $lean_file_hash) || exit 0
  echo "new hash $new_olean_hash"
  leanproject -u "https://oleanstorage.blob.core.windows.net/mathlib/$new_olean_hash.tar.gz" get-cache || true
fi
