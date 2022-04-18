/-
Copyright (c) 2022 Arthur Paulino, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Damiano Testa
-/
import data.polynomial.degree.definitions

/-!  # A tactic for sorting sums  -/

namespace tactic.interactive

open tactic
setup_tactic_parser

/--  Takes an `expr` and returns a list of its summands. -/
meta def get_summands : expr → list expr
| `(%%a + %%b) := get_summands a ++ get_summands b
| a            := [a]

section with_cmp_fn

/--  Let `cmp_fn : expr → expr → bool` be a "compare" function and let `e` be an expression.
`sorted_sum_with_cmp cmp_fn e` returns an ordered sum of the terms of `e`, where
the order is determined using `cmp_fn`.

We use this function for expressions in an additive commutative semigroup. -/
meta def sorted_sum_with_cmp_fn (hyp : option name) (cmp_fn : expr → expr → bool) (e : expr) :
  tactic unit :=
match (get_summands e).qsort cmp_fn with
| ei::es := do
  el' ← es.mfoldl (λ e1 e2, mk_app `has_add.add [e1, e2]) ei,
  e_eq ← mk_app `eq [e, el'],
  n ← get_unused_name,
  assert n e_eq,
  e_eq_fmt ← pp e_eq,
  reflexivity <|>
    `[{ simp only [add_comm, add_assoc, add_left_comm], done, }] <|>
    -- `[{ abel, done, }] <|> -- this works too. it's more robust but also a bit slower
      fail format!"Failed to prove:\n {e_eq_fmt}",
  h ← get_local n,
  match hyp with
  | some loc := do
    hp ← get_local loc,
    rewrite_hyp h hp,
    tactic.clear h
  | none     := do
    rewrite_target h,
    tactic.clear h
  end
| [] := skip
end

-- inductive sort_side | lhs | rhs | both

/-- If the target is an equality, `sort_summands` sorts the summands on either side of the equality.
-/
meta def sort_summands (hyp : option name) (cmp_fn : expr → expr → bool) : tactic unit :=
match hyp with
| none := do
  t ← target,
  match t.is_eq with
  | none          := fail "The goal is not an equality"
  | some (el, er) := do
    sorted_sum_with_cmp_fn hyp cmp_fn el,
    sorted_sum_with_cmp_fn hyp cmp_fn er
  end
| some loc := do
  cloc ← get_local loc,
  tloc ← infer_type cloc,
  match tloc.is_eq with
  | none          := fail "The target is not an equality"
  | some (el, er) := do
    sorted_sum_with_cmp_fn hyp cmp_fn el,
    sorted_sum_with_cmp_fn hyp cmp_fn er
  end
end

end with_cmp_fn

/--  The order on `polynomial.monomial n r`, where monomials are compared by their "exponent" `n`.
If the expression is not a monomial, then the weight is `⊥`. -/
meta def monomial_weight : expr → option ℕ
| a := match a.app_fn with
  | `(coe_fn $ polynomial.monomial %%n) := n.to_nat
  | _ := none
  end

/--  The function we use to compare two `expr`:
* all non-monomials are compared alphabetically;
* all non-monomials are smaller than all monomials;
* bigger monomials have higher exponent.
-/
meta def compare_fn (eₗ eᵣ : expr) : bool :=
match (monomial_weight eₗ, monomial_weight eᵣ) with
| (none, none)     := eₗ.to_string ≤ eᵣ.to_string -- this solution forces an unique ordering
| (_, none)        := false
| (none, _)        := true
| (some l, some r) := l ≤ r
end

-- /--  If we have an expression involving monomials, `sum_sorted_monomials` returns an ordered sum
-- of its terms.  Every summands that is not a monomial appears first, after that, monomials are
-- sorted by increasing size of exponent. -/
-- meta def sum_sorted_monomials (e : expr) : tactic unit :=
-- sorted_sum_with_cmp_fn compare_fn e

-- /--  If the target is an equality involving monomials,
-- then  `sort_monomials_lhs` sorts the summands on the lhs. -/
-- meta def sort_monomials_lhs : tactic unit :=
-- sort_summands sort_side.lhs compare_fn

-- /-- If the target is an equality involving monomials,
-- then  `sort_monomials_rhs` sorts the summands on the rhs. -/
-- meta def sort_monomials_rhs : tactic unit :=
-- sort_summands sort_side.rhs compare_fn

private meta def sort_monomials_core (allow_failure : bool) (hyp : option name) : itactic :=
if allow_failure then sort_summands hyp compare_fn <|> skip else sort_summands hyp compare_fn

/-- If the target is an equality involving monomials,
then  `sort_monomials` sorts the summands on either side of the equality. -/
meta def sort_monomials (locat : parse location) : itactic :=
match locat with
| loc.wildcard := do
  sort_monomials_core tt none,
  ctx ← local_context,
  ctx.mmap (λ e, sort_monomials_core tt (expr.local_pp_name e)),
  skip
| loc.ns names := do
  names.mmap $ sort_monomials_core ff,
  skip
end

end tactic.interactive

open polynomial tactic
open_locale polynomial classical

variables {R : Type*} [semiring R] (f g h : R[X]) {r s t u : R} (r0 : t ≠ 0)

example
  (hp : (monomial 1) u + (g + (monomial 5) 1) + 5 * X + ((monomial 0) s + (monomial 2) t + f) +
  (monomial 8) 1 = (3 * X + (monomial 8) 1 + (monomial 6) (t + 1)) + f + h + ((monomial 0) s +
  (monomial 1) u) + (monomial 5) 1) :
  (monomial 1) u + 5 * X + (g + (monomial 5) 1) + ((monomial 0) s + (monomial 2) t + f) +
  (monomial 8) 1 = (3 * X + (monomial 8) 1 + (monomial 6) (t + 1)) + f + h + ((monomial 0) s +
  (monomial 1) u) + (monomial 5) 1 :=
begin
  -- `convert hp using 1, ac_refl,` works and takes 6s,
  -- `sort_monomials at ⊢ up, assumption` takes under 300ms
  sort_monomials,
  sort_monomials at hp,
  sort_monomials at ⊢ hp, -- does nothing more
  assumption,
  -- sort_monomials_lhs, -- LHS and RHS agree here
  -- sort_monomials_rhs, -- Hmm, both sides change?
  --                     -- Probably, due to the `rw` matching both sides of the equality
  -- symmetry,
  -- sort_monomials_lhs, -- Both sides change again.
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
