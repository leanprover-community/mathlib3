/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import tactic.lint system.io data.list.sort   -- these are required
import all   -- then import everything, to parse the library for failing linters

/-!
# mk_nolint

Defines a function that writes a file containing the names of all declarations
that fail the linting tests in `active_linters`.

This is mainly used in the Travis check for mathlib.

It assumes that files generated by `mk_all.sh` are present.

Usage: `lean --run mk_nolint.lean` writes a file `nolints.txt` in the current directory.
-/

open io io.fs

/-- Defines the list of linters that will be considered. -/
meta def active_linters :=
[`linter.unused_arguments, `linter.dup_namespace, `linter.doc_blame,
 `linter.illegal_constants, `linter.def_lemma, `linter.instance_priority]

/-- Runs when called with `lean --run` -/
meta def main : io unit :=
do (ns, _) ← run_tactic $ lint_mathlib tt tt active_linters tt,
   handle ← mk_file_handle "nolints.txt" mode.write,
   put_str_ln handle "import .all",
   put_str_ln handle "attribute [nolint]",
   (ns.to_list.merge_sort (λ a b, name.lex_cmp a b = ordering.lt)).mmap $
     λ n, put_str_ln handle (to_string n) >> return n,
   close handle
