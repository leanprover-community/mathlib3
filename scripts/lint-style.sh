#!/usr/bin/env bash

# # Style linter

# ## Usage

# Run this script from the root of mathlib using:
# ./scripts/lint-style.sh

# ## Purpose

# The style linter checks for new style issues,
# and maintains a list of exceptions for legacy reasons.
# Ideally, the length of the list of exceptions tends to 0.

# Examples of issues that are checked for are:
# * existence of copyright header
# * existence of module docstrings (in the right place)
# * line length <= 100 (unless URL)

# ## Implementation details

# A Python script `scripts/lint-style.py` that lints the contents of a Lean file.
# This script is called below on all Lean files in the repository.
# Exceptions are maintained in `scripts/style-exceptions.txt`.

touch scripts/style-exceptions.txt

find src archive -name '*.lean' | xargs ./scripts/lint-style.py

