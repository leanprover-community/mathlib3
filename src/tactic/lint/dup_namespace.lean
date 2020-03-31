/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis
-/
import tactic.lint.basic

/-!
# Linter for duplicate namespaces

This file defines the `dup_namespace` linter which checks that there are no
declaration with duplicated namespaces in their name, such as for example
`list.list.monad`.
-/

open tactic

/-- Checks whether a declaration has a namespace twice consecutively in its name -/
private meta def dup_namespace (d : declaration) : tactic (option string) :=
is_instance d.to_name >>= λ is_inst,
return $ let nm := d.to_name.components in if nm.chain' (≠) ∨ is_inst then none
  else let s := (nm.find $ λ n, nm.count n ≥ 2).iget.to_string in
  some $ "The namespace `" ++ s ++ "` is duplicated in the name"

/-- A linter for checking whether a declaration has a namespace twice consecutively in its name. -/
@[linter] meta def linter.dup_namespace : linter :=
{ test := dup_namespace,
  no_errors_found := "No declarations have a duplicate namespace",
  errors_found := "DUPLICATED NAMESPACES IN NAME" }
