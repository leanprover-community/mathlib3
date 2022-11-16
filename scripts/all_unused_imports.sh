# From the root directory of mathlib,
# `scripts/all_unused_imports.sh` will attempt to find all unused imports in all files.
# It is very slow, but could be made much faster if needed.
scripts/mk_all.sh
for file in $(cat src/all.lean | sed -e 's|import ||'); do
  echo "# Unused imports in $file"
  scripts/unused_imports.sh $file
  echo
done
