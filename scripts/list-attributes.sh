#!/usr/bin/env bash

# This script generates the data for mathlib#18164

URL_BASE="https://github.com/leanprover-community/mathlib/blob"
SHA=$(git rev-parse HEAD)

IFS=":"
git grep -n "local attribute \[semireducible\]\|attribute \[irreducible\]" | \
	grep -v 'src/tactic\|src/meta\|test' | \
	while read fn ln rest; do
		grep --silent "SYNCHRONIZED WITH MATHLIB4" $fn || \
			echo "$URL_BASE/$SHA/$fn#L$ln"
	done

