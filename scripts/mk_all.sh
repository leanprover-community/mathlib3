#!/bin/bash
# Makes a file all.lean in all subfolders of src/ importing all files in that folder, including subfolders.
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
for d in $(find $DIR/../src/ -type d)
do
  cd "$d"
  find . -maxdepth 1 -mindepth 1 -name 'all.lean' -prune -o -name '*.lean' -print -o -type d -print |
  sed 's/$/\.all/; s/\.lean\.all//; s/^\.\//       \./; 1s/^      /import/' > all.lean
done
