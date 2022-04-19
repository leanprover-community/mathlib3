/-
Copyright (c) 2022 Arthur Paulino, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Damiano Testa
-/
import data.polynomial.degree.definitions

/-!  # A tactic for sorting sums -/

namespace tactic.interactive

open tactic
setup_tactic_parser

/--  Takes an `expr` and returns a list of its summands. -/
meta def get_summands : expr → list expr
| `(%%a + %%b) := get_summands a ++ get_summands b
| a            := [a]

section with_rel

/--  We sort the elements of the list `l`, making sure that the elements of `t` appear at the
end of the list.

Use as `l.sort_with_top t rel`.
 -/
def _root_.list.sort_with_top {N : Type*} [decidable_eq N] (l t : list N) (rel : N → N → bool) :
  list N :=
let tl := t.dedup.filter (∈ l) in (l.filter (∉ tl)).qsort rel ++ tl

/--  Let `rel : expr → expr → bool` be a relation, `t` a list of expressions and `e` an expression.
`sorted_sum_with_rel rel t e` returns an ordered sum of the terms of `e`, where the order is
determined using the relation `rel`, except that the elements from the list `t` appear reversed and
last in the sum.

We use this function for expressions in an additive commutative semigroup. -/
meta def sorted_sum_with_rel
  (hyp : option name) (rel : expr → expr → bool) (t : list expr) (e : expr) : tactic unit :=
match (get_summands e).sort_with_top t rel with
| eₕ::es := do
  e' ← es.mfoldl (λ eₗ eᵣ, mk_app `has_add.add [eₗ, eᵣ]) eₕ,
  e_eq ← mk_app `eq [e, e'],
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
    get_local loc >>= rewrite_hyp h,
    tactic.clear h
  | none     := do
    rewrite_target h,
    tactic.clear h
  end
| [] := skip
end

/-- Partially traverses an expression in search for a sum of terms.
When `recurse_on_expr` finds a sum, it sorts it using `sorted_sum_with_rel`. -/
meta def recurse_on_expr (t : list expr) (hyp : option name) (rel : expr → expr → bool) :
  expr → tactic unit
| e@`(%%_ + %%_)     := sorted_sum_with_rel hyp rel t e
| (expr.lam _ _ _ e) := recurse_on_expr e
| (expr.pi  _ _ _ e) := recurse_on_expr e
| e                  := e.get_app_args.mmap' recurse_on_expr

/-- Calls `recurse_on_expr` with the right expression, depending on the tactic location. -/
meta def sort_summands (rel : expr → expr → bool) (t : list expr) : option name → tactic unit
| (some hyp) := get_local hyp >>= infer_type >>= recurse_on_expr t hyp rel
| none       := target >>= recurse_on_expr t none rel

end with_rel

/--  The order on `polynomial.monomial n r`, where monomials are compared by their "exponent" `n`.
If the expression is not a monomial, then the weight is `⊥`. -/
meta def monomial_weight (e : expr) : option ℕ :=
match e.app_fn with
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

meta def sort_monomials_core (allow_failure : bool) (t : list expr) (hyp : option name) :
  tactic unit :=
if allow_failure then sort_summands compare_fn t hyp <|> skip
else sort_summands compare_fn t hyp

/-- If the target is an equality involving monomials,
then  `sort_monomials` sorts the summands on either side of the equality. -/
meta def sort_monomials (l : parse pexpr_list_or_texpr?) (locat : parse location) : tactic unit :=
do
  l : list expr ← (l.get_or_else []).mmap to_expr,
  match locat with
  | loc.wildcard := do
    sort_monomials_core tt l none,
    ctx ← local_context,
    ctx.mmap (λ e, sort_monomials_core tt l (expr.local_pp_name e)),
    skip
  | loc.ns names := do
    names.mmap $ sort_monomials_core ff l,
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
  -- `sort_monomials at ⊢ hp, assumption` takes under 300ms
  sort_monomials [g, (5 * X : R[X]), g, 3, f] at ⊢ hp,
  sort_monomials [(5 * X : R[X]), monomial 2 t, monomial 0 s],
  sort_monomials at ⊢ hp,
  assumption,
end

example (hp : f = g) :
  7 + f + (monomial 3 r + 42) + h = monomial 3 r + h + g + 7 + 42 :=
begin
  sort_monomials [f, g],
  congr,
  assumption,
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

-- example :
--   ((monomial 1) u + 5 * X + (g + (monomial 5) 1) + ((monomial 0) s + (monomial 2) t + f) +
--   (monomial 8) 1).nat_degree =
--     ((3 * X + (monomial 8) 1 + (monomial 6) (t + 1)) + f + h + ((monomial 0) s +
--   (monomial 1) u) + (monomial 5) 1).nat_degree :=
-- begin
--   sort_monomials,
-- end

-- example :
--   15 + 5 =
--     ((3 * X + (monomial 8) 1 + (monomial 6) (t + 1)) + f + h + ((monomial 0) s +
--   (monomial 1) u) + (monomial 5) 1).nat_degree :=
-- begin
--   sort_monomials,
-- end
