#!/usr/bin/env bash

# This is a little wrapper around the python script
# lint-copy-mod-doc.py

find src archive -name '*.lean' | xargs ./scripts/lint-copy-mod-doc.py | sort > scripts/copy-mod-doc-exceptions.txt
