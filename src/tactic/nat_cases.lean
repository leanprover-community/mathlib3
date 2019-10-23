/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison

Case bashing on natural numbers.

`nat_cases a ≤ n < b` breaks into the following cases:
`n < a`, one case `n = k` for each `a ≤ k < b`, and `n ≥ b`

`nat_cases n`
1) inspects hypotheses looking for "easy" upper and lower bounds on `n`,
2) calls `nat_cases a ≤ n < b` with appropriate values of `a` and `b`,
3) calls `linarith` to discharge the `n < a` and `n ≥ b` cases.
-/
import tactic.fin_cases
import tactic.linarith
import data.nat.basic

open list

lemma nat.Ico_trichotomy (n a b : ℕ) : n < a ∨ n ≥ b ∨ n ∈ Ico a b :=
begin
  by_cases h₁ : n < a,
  { left, exact h₁ },
  { right,
    by_cases h₂ : n ∈ Ico a b,
    { right, simp only [Ico.mem] at *, cases h₂, split; assumption },
    { left,  simp only  [Ico.mem, not_and, not_lt] at *, exact h₂ h₁ }}
end

namespace tactic
open lean.parser
open interactive interactive.types expr

/--
If you can easily extract a proof that `(%%n < b)` for some
explicit `b : ℕ`, return that `b`, along with the proof.
-/
meta def gives_upper_bound (n e : expr) : tactic (ℕ × expr) :=
do t ← infer_type e,
   match t with
   | `(%%n < %%b) := do b ← eval_expr ℕ b, return (b, e)
   | _ := failed
   end
/--
If you can easily extract a proof that `(%%n ≥ b)` for some
explicit `b : ℕ`, return that `b`, along with the proof.
-/
meta def gives_lower_bound (n e : expr) : tactic (ℕ × expr) :=
do t ← infer_type e,
   match t with
   | `(%%n ≥ %%b) := do b ← eval_expr ℕ b, return (b, e)
   | _ := failed
   end

meta def combine_upper_bounds : option (ℕ × expr) → option (ℕ × expr) → option (ℕ × expr)
| none none := none
| (some (b, prf)) none := some (b, prf)
| none (some (b, prf)) := some (b, prf)
| (some (b₁, prf₁)) (some (b₂, prf₂)) :=
  if b₁ ≤ b₂ then some (b₁, prf₁) else some (b₂, prf₂)

meta def combine_lower_bounds : option (ℕ × expr) → option (ℕ × expr) → option (ℕ × expr)
| none none := none
| (some (b, prf)) none := some (b, prf)
| none (some (b, prf)) := some (b, prf)
| (some (b₁, prf₁)) (some (b₂, prf₂)) :=
  if b₁ ≥ b₂ then some (b₁, prf₁) else some (b₂, prf₂)

meta def update_bounds (n : expr) (bounds : option (ℕ × expr) × option (ℕ × expr)) (e : expr) :
  tactic (option (ℕ × expr) × option (ℕ × expr)) :=
do nlb ← try_core $ gives_lower_bound n e,
   nub ← try_core $ gives_upper_bound n e,
   return (combine_lower_bounds bounds.1 nlb, combine_upper_bounds bounds.2 nub)

meta def get_bounds (n : expr) : tactic (ℕ × expr × ℕ × expr) :=
do
  zero_le ← to_expr ``(zero_le %%n),
  let initial_bounds : option (ℕ × expr) × option (ℕ × expr) := (some (0, zero_le), none),
  lc ← local_context,
  r ← lc.mfoldl (update_bounds n) initial_bounds,
  match r with
  | (_, none) := fail "No upper bound located."
  | (none, _) := fail "No lower bound located."
  | (some (lb, lb_prf), some (ub, ub_prf)) := return (lb, lb_prf, ub, ub_prf)
  end

-- TODO track which hypotheses are relevant for linarith
meta def nat_cases_ineq (n : name) (a b : ℕ) (use_linarith : bool) : tactic unit :=
do n ← get_local n,
   v ← to_expr ``(nat.Ico_trichotomy %%n %%`(a) %%`(b)),
   t ← infer_type v,
   h ← assertv `h t v,
   [(_, [h₁], _), (_, [h₂], _)] ← cases_core h,
   (guard use_linarith >> `[linarith]) <|> rotate_left 1,
   [(_, [h₃], _), (_, [h₄], _)] ← cases_core h₂,
   (guard use_linarith >> `[linarith]) <|> rotate_left 1,
   fin_cases_at none h₄

meta def nat_cases (n : expr) : tactic unit :=
do
(a, a_prf, b, b_prf) ← get_bounds n,
    trace a,
    trace b,
   v ← to_expr ``(nat.Ico_trichotomy %%n %%`(a) %%`(b)),
   t ← infer_type v,
   h ← assertv `h t v,

   [(_, [h₁], _), (_, [h₂], _)] ← cases_core h,
   target >>= trace,
   exact a_prf,
  --  g ← by_contradiction,
  --  linarith.prove_false_by_linarith {} none [a_prf, b_prf, g] <|> rotate_left 1,
   [(_, [h₃], _), (_, [h₄], _)] ← cases_core h₂,
   target >>= trace,
   exact b_prf,
  --  g ← by_contradiction,
  --  linarith.prove_false_by_linarith {} none [a_prf, b_prf, g] <|> rotate_left 1,
   fin_cases_at none h₄


namespace interactive

meta def nat_cases : parse texpr → tactic unit
| e := to_expr e >>= tactic.nat_cases

end interactive

end tactic
