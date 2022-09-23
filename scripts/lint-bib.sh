#!/usr/bin/env bash

set -exo pipefail

bibtool --preserve.key.case=on --preserve.keys=on --pass.comments=on --print.use.tab=off -s \
  -i docs/references.bib -o docs/references.bib
git diff --exit-code
