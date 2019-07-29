#!/bin/bash
# Removes all files named all.lean in the src/ directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
find $DIR/../src/ -name 'all.lean' -delete
