/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/
import data.option.defs data.mllist tactic.core

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

namespace tactic.rewrite_all

/-- Configuration options for rewriting tactics. The options are:
* `try_simp`   (default: `ff`)
* `discharger` (default: `skip`)
* `simplifier` (default: `λ _, failed`)
-/
meta structure cfg extends rewrite_cfg :=
(try_simp   : bool := ff)
(discharger : tactic unit := skip)
 -- Warning: rewrite_search can't produce tactic scripts when the simplifier is used.
(simplifier : expr → tactic (expr × expr) := λ e, failed)

/-- `tracked_rewrite` is the main data structure in the `rewrite_all` suite of rewriting tactics.
A term of type `tracked_rewrite` records
an expression `exp`,
another expression `proof` that is wrapped in the `tactic` monad,
and an optional list of `side`s.
The intuition is that `proof` records a TODO -/
meta structure tracked_rewrite :=
(exp : expr)
(proof : tactic expr)
-- If `addr` is not provided by the underlying implementation of `rewrite_all` (i.e. kabstract)
-- `rewrite_search` will not be able to produce tactic scripts.
(addr : option (list side))

namespace tracked_rewrite

meta def eval (rw : tracked_rewrite) : tactic (expr × expr) :=
do prf ← rw.proof,
   return (rw.exp, prf)

meta def replace_target (rw : tracked_rewrite) : tactic unit :=
do (exp, prf) ← rw.eval,
   tactic.replace_target exp prf

private meta def replace_target_side (new_target : expr) (lam : pexpr) (prf : expr) : tactic unit :=
do prf' ← to_expr ``(congr_arg %%lam %%prf) tt ff,
   tactic.replace_target new_target prf'

meta def replace_target_lhs (rw : tracked_rewrite) : tactic unit :=
do expr.app (expr.app r lhs) rhs ← target,
   (new_lhs, prf) ← rw.eval,
   replace_target_side (r new_lhs rhs) ``(λ L, %%r L %%rhs) prf

meta def replace_target_rhs (rw : tracked_rewrite) : tactic unit :=
do expr.app (expr.app r lhs) rhs ← target,
   (new_rhs, prf) ← rw.eval,
   replace_target_side (r lhs new_rhs) ``(λ R, %%r %%lhs R) prf

variable (h : expr)

meta def replace_hyp (rw : tracked_rewrite) : tactic unit :=
do (exp, prf) ← rw.eval,
   tactic.replace_hyp h exp prf,
   skip

private meta def replace_hyp_side (new_hyp : expr) (lam : pexpr) (prf : expr) : tactic unit :=
do prf' ← to_expr ``(congr_arg %%lam %%prf) tt ff,
   tactic.replace_hyp h new_hyp prf',
   skip

meta def replace_hyp_lhs (rw : tracked_rewrite) : tactic unit :=
do (new_lhs, prf) ← rw.eval,
   expr.app (expr.app r lhs) rhs ← infer_type h,
   replace_hyp_side h (r new_lhs rhs) ``(λ L, %%r L %%rhs) prf,
   skip

meta def replace_hyp_rhs (rw : tracked_rewrite) : tactic unit :=
do (new_rhs, prf) ← rw.eval,
   expr.app (expr.app r lhs) rhs ← infer_type h,
   replace_hyp_side h (r lhs new_rhs) ``(λ R, %%r %%lhs R) prf,
   skip

end tracked_rewrite

end tactic.rewrite_all
