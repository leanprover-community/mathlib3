#!/usr/bin/env bash

# This script can be run locally from the root of mathlib using:
# scripts/lint-copy-mod-doc.sh
# to check whether there are any new copyright header / module doc / line length issues

# This is a little wrapper around the python script
# lint-copy-mod-doc.py

touch scripts/copy-mod-doc-exceptions.txt

find src archive -name '*.lean' | xargs ./scripts/lint-copy-mod-doc.py
