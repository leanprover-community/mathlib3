#!/bin/bash
# Makes a file all.lean in all subfolders of src/ importing all files in that folder,
# including subfolders.
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# Set DIR to the (absolute) directory of this script
for d in $(find $DIR/../src/ -type d)
# For every subfolder of src/ (including src/ itself)
do
  cd "$d" # cd to that directory
  find . -maxdepth 1 -mindepth 1 -name 'all.lean' -prune -o -name '*.lean' -print -o -type d -print |
  # find all files with .lean extension (except all.lean) and all subdirectories
  sed 's/$/\.all/; s/\.lean\.all//; s/^\.\//       \./; 1s/^      /\/- automatically generated file importing all files in this directory and subdirectories. -\/\nimport/' > all.lean
  # Now modify this output so that Lean can parse it. Changes `./foo.lean` to `.foo` and `foodir` to `.foodir.all`. Also adds indentation, a comment and `import`. Write this to `all.lean`
done
