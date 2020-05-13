#!/usr/bin/env bash
# Makes a file src/all.lean importing all files.
cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"/../src

find -name \*.lean -not -name all.lean \
  | sed 's,^\./,,;s,\.lean$,,;s,/,.,g;s,^,import ,' \
  | sort >all.lean
