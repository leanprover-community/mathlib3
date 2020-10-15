#!/usr/bin/env bash

# This script completely regenerates the scripts/copy-mod-doc-exceptions.txt file
# Typically this should only be run by automation.
# Human contributors shouldn't need to run this unless they are making changes to the linting script

# use C locale so that sorting is the same on macOS and Linux
# see https://unix.stackexchange.com/questions/362728/why-does-gnu-sort-sort-differently-on-my-osx-machine-and-linux-machine
find src archive -name '*.lean' | xargs ./scripts/lint-copy-mod-doc.py | LC_ALL=C sort > scripts/copy-mod-doc-exceptions.txt
