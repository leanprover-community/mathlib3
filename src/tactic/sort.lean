/-
Copyright (c) 2022 Arthur Paulino, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Damiano Testa
-/
import data.polynomial.degree.definitions

/-!  # A tactic for sorting sums  -/

namespace tactic

/--  Given an expression `ei` and a list `l : list expr`, returns an `expr` that is
`ei + sum_of_list l`. -/
meta def build_sum (ei : expr) (l : list expr) : tactic expr :=
l.mfoldl (λ e1 e2, mk_app `has_add.add [e1, e2]) ei

/--  Takes an `expr` and returns a list of its summands. -/
meta def get_summands : expr → list expr
| `(%%a + %%b) := get_summands a ++ get_summands b
| a            := [a]

section with_weights
variables {N : Type*} [has_lt N] [decidable_rel (has_lt.lt : N → N → Prop)]

/--  Given an expression `a` and a weight function `wt : expr → N` to a Type `N` with `<`,
`sort_summands_with_weight a wt` returns the list of summands appearing in `a`, sorted using the
order `<`. -/
meta def sort_summands_with_weight (a : expr) (wt : expr → N) : list expr :=
(get_summands a).merge_sort $ function.on_fun (<) wt

/--  Let `wt : expr → N` be a "weight function": any function from `expr` to a Type `N` with a
decidable relation `<`.

Given an expression `e` in an additive commutative semigroup, `sorted_sum_with_weight wt e`
returns an ordered sum of its terms, where the order is determined by applying `wt` to the summands
appearing in `e`. -/
meta def sorted_sum_with_weight (wt : expr → N) (e : expr) : tactic unit :=
match sort_summands_with_weight e wt with
| ei::es := do
  el' ← build_sum ei es,
  e_eq ← mk_app `eq [e, el'],
  n ← get_unused_name,
  assert n e_eq,
  reflexivity <|>
    `[{ simp only [add_comm, add_assoc, add_left_comm], done, }] <|>
      fail "failed to prove {e_eq}", -- how to print this?
  h ← get_local n,
  rewrite_target h,
  clear h
| [] := skip
end

/--  If the target is an equality, `sort_summands_lhs` sorts the summands on the lhs.
-/
meta def sort_summands_lhs (wt : expr → N) : tactic unit :=
do
  -- e ← get_local `h,
  -- t ← infer_type e,
  t ← target,
  match t.is_eq with
  | some (el, er) := sorted_sum_with_weight wt el
  | none          := fail "The goal is not an equality"
  end

/-- If the target is an equality, `sort_summands_rhs` sorts the summands on the rhs.
-/
meta def sort_summands_rhs (wt : expr → N) : tactic unit :=
do
  t ← target,
  match t.is_eq with
  | some (el, er) := sorted_sum_with_weight wt er
  | none          := fail "The goal is not an equality"
  end

/-- If the target is an equality, `sort_summands` sorts the summands on either side of the equality.
-/
meta def sort_summands (wt : expr → N) : tactic unit :=
do
  t ← target,
  match t.is_eq with
  | none          := fail "The goal is not an equality"
  | some (el, er) := do
    sorted_sum_with_weight wt el,
    sorted_sum_with_weight wt er
  end

end with_weights

/--  The order on `polynomial.monomial n r`, where monomials are compared by their "exponent" `n`.
If the expression is not a monomial, then the weight is `⊥`. -/
meta def monomial_weight : expr → with_bot ℕ
| a := match a.app_fn with
  | `(coe_fn $ polynomial.monomial %%n) := n.to_nat
  -- why do I have to remind Lean that this is `with_bot ℕ` and not `option ℕ`?
  | _ := (⊥ : with_bot ℕ)
  end

/--  If we have an expression involving monomials, `sum_sorted_monomials` returns an ordered sum
of its terms.  Every summands that is not a monomial appears first, after that, monomials are
sorted by increasing size of exponent. -/
meta def sum_sorted_monomials (e : expr) : tactic unit :=
sorted_sum_with_weight monomial_weight e

/--  If the target is an equality involving monomials,
then  `sort_monomials_lhs` sorts the summands on the lhs. -/
meta def _root_.sort_monomials_lhs : tactic unit :=
sort_summands_lhs monomial_weight

/-- If the target is an equality involving monomials,
then  `sort_monomials_rhs` sorts the summands on the rhs. -/
meta def _root_.sort_monomials_rhs : tactic unit :=
sort_summands_rhs monomial_weight

/-- If the target is an equality involving monomials,
then  `sort_monomials` sorts the summands on either side of the equality. -/
meta def _root_.sort_monomials : tactic unit :=
sort_summands monomial_weight

end tactic

open polynomial
open_locale polynomial classical

variables {R : Type*} [semiring R] (f g : R[X]) {r s t u : R} (r0 : t ≠ 0)

example : (monomial 1) u + 5 * X + (g + (monomial 5) 1) + ((monomial 0) s + (monomial 2) t + f) +
   (monomial 8) 1 = 5 * X + f + g + (monomial 0) s + (monomial 1) u + (monomial 2) t +
   (monomial 5) 1 + (monomial 8) 1 :=
begin
--  `ac_refl` works and takes 7s,
-- `sort_monomials, refl` takes under 400ms
  sort_monomials, -- LHS and RHS already agree here
  sort_monomials_lhs,
  sort_monomials_rhs,
  symmetry,
  sort_monomials_lhs,
  refl,
end


-- example {R : Type*} [semiring R] (f g : R[X]) {r s t u : R} (r0 : t ≠ 0) :
--   C u * X + (g + X ^ 5) + (C s + C t * X ^ 2 + f) + X ^ 8 = 0 :=
-- begin
--   try { unfold X },
--   try { rw ← C_1 },
--   repeat { rw ← monomial_zero_left },
--   repeat { rw monomial_pow },
--   repeat { rw monomial_mul_monomial },
--   try { simp only [zero_add, add_zero, mul_one, one_mul, one_pow] },
--   sort_monomials,
--   sort_monomials,
--   -- (monomial 0) s + ((monomial 1) u + ((monomial 2) t + ((monomial 5) 1 + (monomial 8) 1))) = 0
-- end
