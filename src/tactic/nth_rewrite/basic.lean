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

namespace tactic

/-- Returns the target of the goal when passed `none`,
otherwise, return the type of `h` in `some h`. -/
meta def target_or_hyp_type : option expr → tactic expr
| none     := target
| (some h) := infer_type h

/-- Replace the target, or a hypothesis, depending on whether `none` or `some h` is given as the
first argument. -/
meta def replace_state_part : option expr → expr → expr → tactic unit
| none     := tactic.replace_target
| (some h) := λ e p, tactic.replace_hyp h e p >> skip

namespace nth_rewrite

/-- Configuration options for nth_rewrite. -/
meta structure cfg extends rewrite_cfg :=
(try_simp   : bool := ff)
(discharger : tactic unit := skip)
 -- Warning: rewrite_search can't produce tactic scripts when the simplifier is used.
(simplifier : expr → tactic (expr × expr) := λ e, failed)

/-- A data structure to track rewrites of subexpressions.
The field `exp` contains the new expression,
while `proof` contains a proof that `exp` is equivalent to the expression that was rewritten. -/
meta structure tracked_rewrite :=
(exp : expr)
(proof : tactic expr)
-- If `addr` is not provided by the underlying implementation of `nth_rewrite` (i.e. kabstract)
-- `rewrite_search` will not be able to produce tactic scripts.
(addr : option (list side))

namespace tracked_rewrite

/-- Postprocess a tracked rewrite into a pair
of a rewritten expression and a proof witness of the rewrite. -/
meta def eval (rw : tracked_rewrite) : tactic (expr × expr) :=
do prf ← rw.proof,
   return (rw.exp, prf)

/-- A helper function for building the proof witness of a rewrite
on one side of an equation of iff. -/
meta def mk_lambda (r lhs rhs : expr) : side → tactic expr
| side.L := do L ← infer_type lhs >>= mk_local_def `L, lambdas [L] (r L rhs)
| side.R := do R ← infer_type rhs >>= mk_local_def `R, lambdas [R] (r lhs R)

/-- A helper function for building the new total expression
starting from a rewrite of one side of an equation or iff. -/
meta def new_exp (exp r lhs rhs : expr) : side → expr
| side.L := r exp rhs
| side.R := r lhs exp

/-- Given a tracked rewrite of (optionally, a side of) the target or a hypothesis,
pass to a new tracked rewrite obtained by replacing the corresponding expression
with the rewritten expression. -/
meta def to_side (rw : tracked_rewrite) (h : option expr) : option side → tactic tracked_rewrite
| none     := return rw
| (some s) := do expr.app (expr.app r lhs) rhs ← target_or_hyp_type h,
                 let prf := do { lam ← mk_lambda r lhs rhs s,
                                 rw.proof >>= mk_congr_arg lam },
                 return ⟨new_exp rw.exp r lhs rhs s, prf, rw.addr.map $ λ l, s :: l⟩

/-- Given a tracked rewrite of (optionally, a side of) the target or a hypothesis,
update the tactic state by replacing the corresponding part of the tactic state
with the rewritten expression. -/
meta def replace (rw : tracked_rewrite) (h : option expr) (s : option side) : tactic unit :=
do (exp, prf) ← rw.to_side h s >>= tracked_rewrite.eval,
   replace_state_part h exp prf

end tracked_rewrite

end nth_rewrite

end tactic
