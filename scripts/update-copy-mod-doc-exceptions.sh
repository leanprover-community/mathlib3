#!/usr/bin/env bash

# This script completely regenerates the scripts/copy-mod-doc-exceptions.txt file
# Typically this should only be run by automation.
# Human contributors shouldn't need to run this unless they are making changes to the linting script

# Replace the current exceptions file with an empty file
> scripts/copy-mod-doc-exceptions.txt

# use C locale so that sorting is the same on macOS and Linux
# see https://unix.stackexchange.com/questions/362728/why-does-gnu-sort-sort-differently-on-my-osx-machine-and-linux-machine
LC_ALL=C find src archive -name '*.lean' | xargs ./scripts/lint-copy-mod-doc.py | sort > scripts/copy-mod-doc-exceptions.txt
