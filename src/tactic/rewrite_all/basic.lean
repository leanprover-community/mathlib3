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

meta def mk_lambda_lhs (r lhs rhs : expr) : tactic expr :=
do t ← infer_type lhs,
   L ← mk_local_def `L t,
   lambdas [L] (r L rhs)

meta def mk_lambda_rhs (r lhs rhs : expr) : tactic expr :=
do t ← infer_type rhs,
   R ← mk_local_def `R t,
   lambdas [R] (r lhs R)

meta def replace' : option expr → expr → expr → tactic unit
| none     := tactic.replace_target
| (some h) := λ e p, tactic.replace_hyp h e p >> skip

meta def replace (h : option expr) (rw : tracked_rewrite) : tactic unit :=
do (exp, prf) ← rw.eval,
   replace' h exp prf

meta def replace_hyp (h : expr) (rw : tracked_rewrite) : tactic unit :=
replace h rw

meta def replace_target (rw : tracked_rewrite) : tactic unit :=
replace none rw

private meta def replace_side (h : option expr) (new_target lam prf : expr) : tactic unit :=
do prf' ← mk_congr_arg lam prf,
   replace' h new_target prf'

meta def target_or_hyp_type : option expr → tactic expr
| none     := target
| (some h) := infer_type h

meta def replace_lhs (h : option expr) (rw : tracked_rewrite) : tactic unit :=
do expr.app (expr.app r lhs) rhs ← target_or_hyp_type h,
   (new_lhs, prf) ← rw.eval,
   lam ← mk_lambda_lhs r lhs rhs,
   replace_side h (r new_lhs rhs) lam prf

meta def replace_rhs (h : option expr) (rw : tracked_rewrite) : tactic unit :=
do expr.app (expr.app r lhs) rhs ← target_or_hyp_type h,
   (new_rhs, prf) ← rw.eval,
   lam ← mk_lambda_rhs r lhs rhs,
   replace_side h (r lhs new_rhs) lam prf

end tracked_rewrite

end tactic.rewrite_all
