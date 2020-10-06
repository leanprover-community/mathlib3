#!/usr/bin/env bash

# This is a little wrapper around the python script
# lint-copy-mod-doc.py

# we want an empty "exceptions" array in lint-copy-mod-doc.py
> scripts/copy-mod-doc-exceptions-short.txt

find src archive -name '*.lean' | xargs ./scripts/lint-copy-mod-doc.py | sort > scripts/copy-mod-doc-exceptions.txt

rm scripts/copy-mod-doc-exceptions-short.txt
