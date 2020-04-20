/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/
import data.option.defs data.mllist tactic.core

namespace tactic

/-- Returns the target of the goal when passed `none`,
otherwise, return the type of `h` in `some h`. -/
meta def target_or_hyp_type : option expr → tactic expr
| none     := target
| (some h) := infer_type h

/-- Replace the target, or a hypothesis, depending on whether `none` or `some h` is given as the
first argument. -/
meta def replace_in_state : option expr → expr → expr → tactic unit
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

private def rel_descent_instructions : side → list side
| side.L := [side.L, side.R]
| side.R := [side.R]

/-- Given a tracked rewrite of (optionally, a side under a relation of) the target or a hypothesis,
produce a new tracked rewrite obtained by replacing the corresponding expression with the rewritten
expression. -/
meta def to_rel_side (rw : tracked_rewrite) (h : option expr) : option side → tactic tracked_rewrite
| none     := return rw
| (some s) := do e ← target_or_hyp_type h,
                 (ln, _) ← expr_lens.entire.descend e (rel_descent_instructions s),
                 return ⟨ln.fill rw.exp, rw.proof >>= ln.congr, rw.addr.map $ λ l, s :: l⟩

/-- Given a tracked rewrite of (optionally, a side under a relation of) the target or a hypothesis,
update the tactic state by replacing the corresponding part of the tactic state with the rewritten
expression. -/
meta def replace (rw : tracked_rewrite) (s : option side) (h : option expr) : tactic unit :=
do rw ← rw.to_rel_side h s,
   rw.proof >>= replace_in_state h rw.exp

end tracked_rewrite

end nth_rewrite

end tactic
