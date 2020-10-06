#!/usr/bin/env bash

# This is a little wrapper around the python script
# lint-copy-mod-doc.py

touch scripts/copy-mod-doc-exceptions.txt

cut -d: -f1,3 < scripts/copy-mod-doc-exceptions.txt > scripts/copy-mod-doc-exceptions-short.txt

find src archive -name '*.lean' | xargs ./scripts/lint-copy-mod-doc.py

rm scripts/copy-mod-doc-exceptions-short.txt
