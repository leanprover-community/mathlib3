/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison
-/
import tactic.basic

namespace tactic

meta def apply_assumption
  (asms : tactic (list expr) := local_context)
  (tac : tactic unit := skip) : tactic unit :=
do { ctx ← asms,
     ctx.any_of (λ H, apply_thorough H >> tac) } <|>
do { exfalso,
     ctx ← asms,
     ctx.any_of (λ H, apply_thorough H >> tac) }
<|> fail "assumption tactic failed"

meta def solve_by_elim_aux (discharger : tactic unit) (asms : tactic (list expr))  : ℕ → tactic unit
| 0 := done
| (n + 1) := discharger <|> (apply_assumption asms $ solve_by_elim_aux n)

meta structure by_elim_opt :=
  (discharger : tactic unit := done)
  (assumptions : tactic (list expr) := local_context)
  (max_rep : ℕ := 3)

meta def solve_by_elim (opt : by_elim_opt := { }) : tactic unit :=
do
  tactic.fail_if_no_goals,
  focus1 $
    solve_by_elim_aux opt.discharger opt.assumptions opt.max_rep

end tactic
