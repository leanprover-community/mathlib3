#!/bin/bash
# Removes all files named all.lean in the src/ directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
find $DIR/../src/ -name 'all.lean' -delete -o -name 'all.olean' -delete
# Removes src/sanity_check_mathlib.lean, which is also created by `mk_all.sh`
rm $DIR/../src/sanity_check_mathlib.lean
