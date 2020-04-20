/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/
import data.option.defs data.mllist tactic.core
import .debug
open tactic

/-- Inductive type with two constructors `L` and `R`,
that represent the left and right hand sides of equations and iffs.

This type is used in the development of rewriting tactics such as
`nth_rewrite`, and `rewrite_search` (not currently in mathlib). -/
@[derive decidable_eq, derive inhabited]
inductive side
| L
| R

/-- Involution on `side`, swaps `L` and `R`. -/
def side.other : side → side
| side.L := side.R
| side.R := side.L

/-- String representation of `side`. -/
def side.to_string : side → string
| side.L := "L"
| side.R := "R"

instance : has_to_string side := ⟨side.to_string⟩

namespace tactic.nth_rewrite

meta structure cfg extends rewrite_cfg :=
(try_simp   : bool := ff)
(discharger : tactic unit := skip)
 -- Warning: rewrite_search can't produce tactic scripts when the simplifier is used.
(simplifier : expr → tactic (expr × expr) := λ e, failed)

meta structure tracked_rewrite :=
(exp : expr)
(proof : tactic expr)
-- If `addr` is not provided by the underlying implementation of `nth_rewrite` (i.e. kabstract)
-- `rewrite_search` will not be able to produce tactic scripts.
(addr : option (list side))

meta def tracked_rewrite.eval (rw : tracked_rewrite) : tactic (expr × expr) :=
do prf ← rw.proof,
   return (rw.exp, prf)

end tactic.nth_rewrite
