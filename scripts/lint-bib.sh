#!/usr/bin/env bash

set -exo pipefail
# https://leanprover-community.github.io/contribute/doc.html#citing-other-works
bibtool --preserve.key.case=on --preserve.keys=on --pass.comments=on --print.use.tab=off -s \
  -i docs/references.bib -o docs/references.bib
git diff --exit-code
