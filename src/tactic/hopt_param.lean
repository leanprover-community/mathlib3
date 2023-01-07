/-
Copyright (c) 2022 Yaël Dillies, Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Wieser
-/

/-!
# Heterogeneous optional parameter

This file provides a heterogeneous version of `opt_param` for use in structure defaults.

The associated tactic `solve_default` allows solving proof obligations involving default field
values in terms of previous structure fields.

The syntax is to make the type of the defaulted field
`hopt_param the_type the_default . solve_default` where `the_type` is the type you actually want for
the field, and `the_default` is the default value (often, proof) for it.

The point is that `the_default` does **not** have to be of type `the_type` at the time the structure
is declared, but only when constructing an instance of the structure.
-/

/-- Gadget for optional parameter support. -/
@[reducible] def hopt_param {α β : Sort*} (a : α) (b : β) : α := a

/-- Return `b` if the goal is `hopt_param a b`. -/
meta def try_hopt_param : command :=
do
  `(hopt_param %%a %%b) ← tactic.target,
  tactic.exact b

/-- Return `b` if the goal is `hopt_param a b`.

This can be used in structure declarations to alleviate proof obligations which can be derived from
other fields which themselves have a default value.
```
structure foo :=
(bar : ℕ)
(bar_eq : bar = 37)
(baz : ℕ := bar)
(baz_eq : hopt_param (baz = 37) bar_eq . solve_default)

/-- `baz_eq` is automatically proved using `bar_eq` because `baz` wasn't changed from its default
value `bar. -/
example : foo :=
{ bar := if 2 = 2 then 37 else 0,
  bar_eq := if_pos rfl }
``` -/
meta def solve_default : command :=
try_hopt_param <|> tactic.fail "A previous structure field was changed from its default value, so
  `solve_default` cannot solve the proof obligation automatically."
