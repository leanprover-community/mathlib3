#!/usr/bin/env bash
# Usage: mk_all.sh [subdirectory]
#
# Examples:
#   ./scripts/mk_all.sh
#   ./scripts/mk_all.sh data/real
#
# Makes a mathlib/src/$directory/all.lean importing all files inside $directory.
# If $directory is omitted, creates `mathlib/src/all.lean`.

cd "$( dirname "${BASH_SOURCE[0]}" )"/../src
if [[ $# = 1 ]]; then
  dir="$1"
else
  dir="."
fi

find "$dir" -name \*.lean -not -name all.lean \
  | sed 's,^\./,,;s,\.lean$,,;s,/,.,g;s,^,import ,' \
  | sort >"$dir"/all.lean
