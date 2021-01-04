#!/usr/bin/env bash

# This script can be run locally from the root of mathlib using:
# scripts/lint-style.sh
# to check whether there are any new style issues, such as:
# copyright header / module doc / line length issues

# This is a little wrapper around the python script
# lint-style.py

touch scripts/style-exceptions.txt

find src archive -name '*.lean' | xargs ./scripts/lint-style.py
