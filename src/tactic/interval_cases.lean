/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison

Case bashing on natural numbers.

`nat_cases n`
1) inspects hypotheses looking for "easy" upper and lower bounds on `n`,
2) calls `nat_cases a ≤ n < b` with appropriate values of `a` and `b`,
3) discharges the `n < a` and `n ≥ b` cases using the previously found bounds.

`nat_cases a ≤ n < b` breaks into the following cases:
`n < a`, one case `n = k` for each `a ≤ k < b`, and `n ≥ b`,
and then attempts to use `linarith` to discharge the inequalities.

-/
import tactic.fin_cases
-- import tactic.linarith
import data.nat.basic
import data.fintype.intervals
import order.bounded_lattice

open set

namespace tactic

namespace interval_cases

/--
If `e` easily implies `(%%n < %%b)`
for some explicit `b`,
return that `b`, as a rational number, along with the proof.
-/
-- We use `expr.to_rat` merely to decide if an `expr` is an explicit number.
-- It would be more natural to use `expr.to_int`, but that hasn't been implemented.
meta def gives_upper_bound (n e : expr) : tactic (ℚ × expr) :=
do t ← infer_type e,
   match t with
   | `(%%n < %%b) := do b ← b.to_rat, return (b, e)
   | `(%%b > %%n) := do b ← b.to_rat, return (b, e)
   | `(%%n ≤ %%b) := do
      b ← b.to_rat,
      tn ← infer_type n,
      e ← match tn with
      | `(ℕ) := to_expr ``(nat.lt_add_one_iff.mpr %%e)
      | `(ℤ) := to_expr ``(int.lt_add_one_iff.mpr %%e)
      | _ := failed
      end,
      return (b + 1, e)
   | `(%%b ≥ %%n) := do
      b ← b.to_rat,
      tn ← infer_type n,
      e ← match tn with
      | `(ℕ) := to_expr ``(nat.lt_add_one_iff.mpr %%e)
      | `(ℤ) := to_expr ``(int.lt_add_one_iff.mpr %%e)
      | _ := failed
      end,
      return (b + 1, e)
   | _ := failed
   end

/--
If `e` easily implies `(%%n ≥ %%b)`
for some explicit `b`,
return that `b`, as a rational number, and the proof.
-/
meta def gives_lower_bound (n e : expr) : tactic (ℚ × expr) :=
do t ← infer_type e,
   match t with
   | `(%%n ≥ %%b) := do b ← b.to_rat, return (b, e)
   | `(%%b ≤ %%n) := do b ← b.to_rat, return (b, e)
   | `(%%n > %%b) := do
      b ← b.to_rat,
      tn ← infer_type n,
      e ← match tn with
      | `(ℕ) := to_expr ``(nat.add_one_le_iff.mpr %%e)
      | `(ℤ) := to_expr ``(int.add_one_le_iff.mpr %%e)
      | _ := failed
      end,
      return (b + 1, e)
   | `(%%b < %%n) := do
      b ← b.to_rat,
      tn ← infer_type n,
      e ← match tn with
      | `(ℕ) := to_expr ``(nat.add_one_le_iff.mpr %%e)
      | `(ℤ) := to_expr ``(int.add_one_le_iff.mpr %%e)
      | _ := failed
      end,
      return (b + 1, e)
   | _ := failed
   end

/-- Combine two upper bounds. -/
meta def combine_upper_bounds : option (ℚ × expr) → option (ℚ × expr) → tactic (option (ℚ × expr))
| none none := return none
| (some (b, prf)) none := return $ some (b, prf)
| none (some (b, prf)) := return $ some (b, prf)
| (some (b₁, prf₁)) (some (b₂, prf₂)) :=
  return $ if b₁ ≤ b₂ then some (b₁, prf₁) else some (b₂, prf₂)

/-- Combine two lower bounds. -/
meta def combine_lower_bounds : option expr → option expr → tactic (option expr)
| none none := return $ none
| (some prf) none := return $ some prf
| none (some prf) := return $ some prf
| (some prf₁) (some prf₂) :=
  do prf ← to_expr ``(max_le %%prf₁ %%prf₂),
  return $ some prf

/-- Inspect a given expression, using it to update a set of upper and lower bounds on `n`. -/
meta def update_bounds (n : expr) (bounds : option expr × option (ℚ × expr)) (e : expr) :
  tactic (option expr × option (ℚ × expr)) :=
do nlb ← try_core $ gives_lower_bound n e,
   nub ← try_core $ gives_upper_bound n e,
   clb ← combine_lower_bounds bounds.1 (nlb.map prod.snd),
   cub ← combine_upper_bounds bounds.2 nub,
   return (clb, cub)

meta def initial_lower_bound (n : expr) : tactic expr :=
do e ← to_expr ``(@lattice.bot_le _ _ %%n),
   t ← infer_type e,
   match t with
   -- This time we use `eval_expr`, because `to_rat` is going to choke on `⊥`.
   | `(%%b ≤ %%n) := do return e
   | _ := failed
   end

meta def initial_upper_bound (n : expr) : tactic (ℚ × expr) :=
do e ← to_expr ``(@lattice.le_top _ _ %%n),
   match e with
   | `(%%n ≤ %%b) := do
     b ← eval_expr ℕ b,
     tn ← infer_type n,
     e ← match tn with
     | `(ℕ) := to_expr ``(nat.add_one_le_iff.mpr %%e)
     | `(ℤ) := to_expr ``(int.add_one_le_iff.mpr %%e)
     | _ := failed
     end,
     return (b + 1, e)
   | _ := failed
   end

/-- Inspect the local hypotheses for upper and lower bounds on a variable `n`. -/
meta def get_bounds (n : expr) : tactic (expr × ℚ × expr) :=
do
  hl ← try_core (initial_lower_bound n),
  hu ← try_core (initial_upper_bound n),
  lc ← local_context,
  r ← lc.mfoldl (update_bounds n) (hl, hu),
  match r with
  | (_, none) := fail "No upper bound located."
  | (none, _) := fail "No lower bound located."
  | (some lb_prf, some (ub, ub_prf)) := return (lb_prf, ub, ub_prf)
  end

def set_elems {α} [decidable_eq α] (s : set α) [fintype s] : finset α :=
(fintype.elems s).image subtype.val

lemma mem_set_elems {α} [decidable_eq α] (s : set α) [fintype s] {a : α} (h : a ∈ s) :
  a ∈ set_elems s :=
finset.mem_image.2 ⟨⟨a, h⟩, fintype.complete _, rfl⟩

end interval_cases

open interval_cases

meta def interval_cases_using (hl hu : expr) : tactic unit :=
to_expr ``(mem_set_elems (Ico _ _) ⟨%%hl, %%hu⟩) >>= note_anon >>= fin_cases_at none

setup_tactic_parser

namespace interactive

meta def interval_cases_using (hl hu : parse ident) : tactic unit :=
do [hl, hu] ← [hl, hu].mmap get_local,
   tactic.interval_cases_using hl hu

meta def interval_cases (n : parse texpr) : tactic unit :=
do n ← to_expr n,
   (hl, _, hu) ← get_bounds n,
   tactic.interval_cases_using hl hu

end interactive

end tactic
