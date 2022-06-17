/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/
import tactic.core

open tactic

@[derive decidable_eq, derive inhabited]
inductive side
| L
| R

def side.other : side → side
| side.L := side.R
| side.R := side.L

def side.to_string : side → string
| side.L := "L"
| side.R := "R"

instance : has_to_string side := ⟨side.to_string⟩

namespace tactic.rewrite_all

meta structure cfg extends rewrite_cfg :=
(try_simp   : bool := ff)
(discharger : tactic unit := skip)
 -- Warning: rewrite_search can't produce tactic scripts when the simplifier is used.
(simplifier : expr → tactic (expr × expr) := λ e, failed)

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

private meta def replace_target_side (new_target lam : pexpr) (prf : expr) : tactic unit :=
do new_target ← to_expr new_target tt ff,
   prf' ← to_expr ``(congr_arg %%lam %%prf) tt ff,
   tactic.replace_target new_target prf'

meta def replace_target_lhs (rw : tracked_rewrite) : tactic unit :=
do (new_lhs, prf) ← rw.eval,
   `(%%_ = %%rhs) ← target,
   replace_target_side ``(%%new_lhs = %%rhs) ``(λ L, L = %%rhs) prf

meta def replace_target_rhs (rw : tracked_rewrite) : tactic unit :=
do (new_rhs, prf) ← rw.eval,
   `(%%lhs = %%_) ← target,
   replace_target_side ``(%%lhs = %%new_rhs) ``(λ R, %%lhs = R) prf

end tracked_rewrite

end tactic.rewrite_all
