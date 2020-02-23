#!/bin/bash
# Makes a file all.lean in all subfolders of src/ importing all files in that folder,
# including subfolders.
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# Set DIR to the (absolute) directory of this script
for d in $(find $DIR/../src/ -type d)
# For every subfolder of src/ (including src/ itself)
do
  cd "$d" # cd to that directory
  echo "/- automatically generated file importing all files in this directory and subdirectories. -/" > all.lean
  find . -maxdepth 1 -mindepth 1 -name 'all.lean' -prune -o -name 'lint_mathlib.lean' -prune -o -name '.*' -prune -o -name '*.lean' -print -o -type d -print |
  # find all non-hidden files with the .lean extension (except all.lean) and all subdirectories
  sed 's/$/\.all/; s/\.lean\.all//; s/^\.\//       \./; 1s/^      /import/' >> all.lean
  # Now modify this output so that Lean can parse it. Changes `./foo.lean` to `.foo` and `foodir` to `.foodir.all`. Also adds indentation, a comment and `import`. Write this to `all.lean`
done

nolint=0
while getopts 't' opt; do
  case $opt in
    t) nolint=1 ;;
    *) echo 'Error in command line parsing' >&2
       exit 1
  esac
done

cd $DIR/../src/
if [ "$nolint" -eq 1 ]; then
  cp ../scripts/nolints.txt ./nolints.lean
  cat <<EOT > lint_mathlib.lean
import .nolints
EOT
else
  cat <<EOT > lint_mathlib.lean
import all
EOT
fi

cat <<EOT >> lint_mathlib.lean

open nat -- need to do something before running a command

#lint_mathlib- only unused_arguments dup_namespace doc_blame ge_or_gt def_lemma instance_priority
  impossible_instance incorrect_type_class_argument dangerous_instance inhabited_nonempty simp_nf
EOT
