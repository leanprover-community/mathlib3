#!/usr/bin/env bash

# This script generates the data for mathlib#18164

URL_BASE="https://github.com/leanprover-community/mathlib/blob"
SHA=$(git rev-parse HEAD)

IFS=":"
git grep -n "local attribute \[semireducible\]\|attribute \[irreducible\]" | \
while read fn ln rest; do echo "$URL_BASE/$SHA/$fn#L$ln" ; done

