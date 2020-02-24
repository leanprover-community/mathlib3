/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison

Case bashing on variables in finite intervals.

`interval_cases n`
1) inspects hypotheses looking for lower and upper bounds of the form `a ≤ n` and `n < b`
   (although in `ℕ`, `ℤ`, and `ℕ+` bounds of the form `a < n` and `n ≤ b` are also allowed)
2) calls `fin_cases` on the synthesised hypothesis `n ∈ set.Ico a b`,
   assuming an appropriate `fintype` instance can be found for the type of `n`.

`interval_cases n using hl hu` does not search the local context for relevant
hypotheses, but rather uses only the specified pair of hypotheses for a lower and upper bound.
-/
import tactic.fin_cases
import data.nat.basic
import data.fintype.intervals
import order.bounded_lattice

open set

namespace tactic

namespace interval_cases

/--
If `e` easily implies `(%%n < %%b)`
for some explicit `b`,
return that proof.
-/
-- We use `expr.to_rat` merely to decide if an `expr` is an explicit number.
-- It would be more natural to use `expr.to_int`, but that hasn't been implemented.
meta def gives_upper_bound (n e : expr) : tactic expr :=
do t ← infer_type e,
   match t with
   | `(%%n < %%b) := do b ← b.to_rat, return e
   | `(%%b > %%n) := do b ← b.to_rat, return e
   | `(%%n ≤ %%b) := do
      b ← b.to_rat,
      tn ← infer_type n,
      match tn with
      | `(ℕ) := to_expr ``(nat.lt_add_one_iff.mpr %%e)
      | `(ℕ+) := to_expr ``(pnat.lt_add_one_iff.mpr %%e)
      | `(ℤ) := to_expr ``(int.lt_add_one_iff.mpr %%e)
      | _ := failed
      end
   | `(%%b ≥ %%n) := do
      b ← b.to_rat,
      tn ← infer_type n,
      match tn with
      | `(ℕ) := to_expr ``(nat.lt_add_one_iff.mpr %%e)
      | `(ℕ+) := to_expr ``(pnat.lt_add_one_iff.mpr %%e)
      | `(ℤ) := to_expr ``(int.lt_add_one_iff.mpr %%e)
      | _ := failed
      end
   | _ := failed
   end

/--
If `e` easily implies `(%%n ≥ %%b)`
for some explicit `b`,
return that proof.
-/
meta def gives_lower_bound (n e : expr) : tactic expr :=
do t ← infer_type e,
   match t with
   | `(%%n ≥ %%b) := do b ← b.to_rat, return e
   | `(%%b ≤ %%n) := do b ← b.to_rat, return e
   | `(%%n > %%b) := do
      b ← b.to_rat,
      tn ← infer_type n,
      match tn with
      | `(ℕ) := to_expr ``(nat.add_one_le_iff.mpr %%e)
      | `(ℕ+) := to_expr ``(pnat.add_one_le_iff.mpr %%e)
      | `(ℤ) := to_expr ``(int.add_one_le_iff.mpr %%e)
      | _ := failed
      end
   | `(%%b < %%n) := do
      b ← b.to_rat,
      tn ← infer_type n,
      match tn with
      | `(ℕ) := to_expr ``(nat.add_one_le_iff.mpr %%e)
      | `(ℕ+) := to_expr ``(pnat.add_one_le_iff.mpr %%e)
      | `(ℤ) := to_expr ``(int.add_one_le_iff.mpr %%e)
      | _ := failed
      end
   | _ := failed
   end

/-- Combine two upper bounds. -/
meta def combine_upper_bounds : option expr → option expr → tactic (option expr)
| none none := return none
| (some prf) none := return $ some prf
| none (some prf) := return $ some prf
| (some prf₁) (some prf₂) :=
  do option.some <$> to_expr ``(lt_min %%prf₁ %%prf₂)

/-- Combine two lower bounds. -/
meta def combine_lower_bounds : option expr → option expr → tactic (option expr)
| none none := return $ none
| (some prf) none := return $ some prf
| none (some prf) := return $ some prf
| (some prf₁) (some prf₂) :=
  do option.some <$> to_expr ``(max_le %%prf₁ %%prf₂)

/-- Inspect a given expression, using it to update a set of upper and lower bounds on `n`. -/
meta def update_bounds (n : expr) (bounds : option expr × option expr) (e : expr) :
  tactic (option expr × option expr) :=
do nlb ← try_core $ gives_lower_bound n e,
   nub ← try_core $ gives_upper_bound n e,
   clb ← combine_lower_bounds bounds.1 nlb,
   cub ← combine_upper_bounds bounds.2 nub,
   return (clb, cub)

meta def initial_lower_bound (n : expr) : tactic expr :=
do e ← to_expr ``(@lattice.bot_le _ _ %%n),
   t ← infer_type e,
   match t with
   | `(%%b ≤ %%n) := do return e
   | _ := failed
   end

meta def initial_upper_bound (n : expr) : tactic expr :=
do e ← to_expr ``(@lattice.le_top _ _ %%n),
   match e with
   | `(%%n ≤ %%b) := do
     tn ← infer_type n,
     e ← match tn with
     | `(ℕ) := to_expr ``(nat.add_one_le_iff.mpr %%e)
     | `(ℕ+) := to_expr ``(pnat.add_one_le_iff.mpr %%e)
     | `(ℤ) := to_expr ``(int.add_one_le_iff.mpr %%e)
     | _ := failed
     end,
     return e
   | _ := failed
   end

/-- Inspect the local hypotheses for upper and lower bounds on a variable `n`. -/
meta def get_bounds (n : expr) : tactic (expr × expr) :=
do
  hl ← try_core (initial_lower_bound n),
  hu ← try_core (initial_upper_bound n),
  lc ← local_context,
  r ← lc.mfoldl (update_bounds n) (hl, hu),
  match r with
  | (_, none) := fail "No upper bound located."
  | (none, _) := fail "No lower bound located."
  | (some lb_prf, some ub_prf) := return (lb_prf, ub_prf)
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
   (hl, hu) ← get_bounds n,
   tactic.interval_cases_using hl hu

end interactive

end tactic
