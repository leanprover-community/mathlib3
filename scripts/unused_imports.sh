# From the root directory of mathlib, `scripts/unused_imports.sh topology.metric_space.basic`
# will report unused imports in `topology.metric_space.basic`.
# Be careful that you may need to restore these imports in later files.

# Implementation note: we could do this much more efficiently.
# `scripts/modules_used.lean` lists all modules used by the given module;
# for this script's purposes, we should not recursively scan declarations,
# but just check that some declaration in the current file refers
# to some declaration in each of the imports.

tmp_dir=$(mktemp -d -t ci-XXXXXXXXXX)
file=src/$(echo $1 | sed -e 's|\.|/|g').lean
lean --deps $file | grep -v .elan | sed -e 's|.*src/||' -e 's|\.olean||' -e 's|/|.|g' | sort > $tmp_dir/deps
lean --run scripts/modules_used.lean $1 2>&1 >/dev/null | grep -v "Error while processing" | sort > $tmp_dir/used
grep -Fvxf $tmp_dir/used $tmp_dir/deps
