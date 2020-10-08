#!/usr/bin/env bash

# This is a little wrapper around the python script
# lint-copy-mod-doc.py

touch scripts/copy-mod-doc-exceptions.txt

find src archive -name '*.lean' | xargs ./scripts/lint-copy-mod-doc.py
