/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis
-/
import tactic.lint.basic

/-!
# Linter for correct usage of `lemma`/`def`

This file defines the `def_lemma` linter which checks that a declaration is a
lemma iff its type is a proposition.
-/

open tactic

/--
Checks whether the correct declaration constructor (definition or theorem) by
comparing it to its sort. Instances will not be printed.

This test is not very quick: maybe we can speed-up testing that something is a proposition?
This takes almost all of the execution time.
-/
private meta def incorrect_def_lemma (d : declaration) : tactic (option string) :=
  if d.is_constant ∨ d.is_axiom
  then return none else do
    is_instance_d ← is_instance d.to_name,
    if is_instance_d then return none else do
      -- the following seems to be a little quicker than `is_prop d.type`.
      expr.sort n ← infer_type d.type, return $
      if d.is_theorem ↔ n = level.zero then none
      else if (d.is_definition : bool) then "is a def, should be a lemma/theorem"
      else "is a lemma/theorem, should be a def"

/-- A linter for checking whether the correct declaration constructor (definition or theorem)
has been used. -/
@[linter] meta def linter.def_lemma : linter :=
{ test := incorrect_def_lemma,
  no_errors_found := "All declarations correctly marked as def/lemma",
  errors_found := "INCORRECT DEF/LEMMA" }

attribute [nolint def_lemma] classical.dec classical.dec_pred classical.dec_rel classical.dec_eq
