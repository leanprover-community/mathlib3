/-
Copyright (c) 2022 Arthur Paulino, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Damiano Testa
-/
import tactic.core
import data.polynomial.basic

/-!  # `sort_summands`, a tactic for sorting sums

Calling `sort_summands` will recursively look inside the goal for expressions involving a sum.
Whenever it finds one, it will sort its terms following a heuristic.  Right now, the heuristic
is somewhat crude: if an individual summand is of the exact form `monomial n r`, with `n` a numeral,
then `monomial n r` will in the last segment and this segment is sorted by increasing value of `n`.
The remaining terms appear at the beginning of the sum and are sorted alphabetically.

To allow for more flexibility, `sort_summands` takes an optional argument that can be either a
single term or a list of terms.  Calling `sort_summands f` or `sort_summands [f,.., g]` performs the
sorting, except that the explicitly given terms appear last in the final sum (repetitions and
inexistent terms are ignored).

Finally, `sort_summands` can also be targeted to a hypothesis.  If `hp` is in the local context,
`sort_summands [f, g] at hp` performs the rearranging at `hp`.


##  Future work

To add better heuristics, an easy approach is to change the definition of `compare_fn`.
Right now, it simply does a case-split: we compare two expressions alphabetically, unless they are
both `monomial <deg> <coe>ff`, in which case, we place the term last and we use `<deg>` to further
compare.

* Allow for pattern-matching in the list of terms?
* Allow to pass `[f, -g, h, -i]` to mean that `f, h` come last and `g i` come first?
  The `-` could be problematic if the expressions involve `neg`.
* Improve sorting heuristic?
* Add support for `neg` and additive groups?
* Allow the option of not changing the given order, except for the explicitly listed terms?
  E.g. `sort_summands only [f, g]`, extracts `f` and `g`, placing them last, but leaving the rest
  unchanged (except for the parenthesis, which will be straightened).
* Add optional different operations than `+`, most notably `*`?
* Allow custom ordering?  E.g. `sort_summands using my_rel`, where `my_rel : N → N → Prop` is a
  relation on a type (with `+`), and, if `sort_summands` encounters a sum of terms of type `N`,
  then it will ask the user to prove the required sorting.
 -/

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
meta def sort_summands_aux (rel : expr → expr → bool) (t : list expr) : option name → tactic unit
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

/--  A version of `sort_summands_aux` that allows failure, if `allow_failure = tt`. -/
meta def sort_summands_core (allow_failure : bool) (t : list expr) (hyp : option name) :
  tactic unit :=
if allow_failure then sort_summands_aux compare_fn t hyp <|> skip
else sort_summands_aux compare_fn t hyp

/-- If the target is an equality involving summands,
then  `sort_summands` sorts the summands on either side of the equality. -/
meta def sort_summands (l : parse pexpr_list_or_texpr?) (locat : parse location) : tactic unit :=
do
  l : list expr ← (l.get_or_else []).mmap to_expr,
  match locat with
  | loc.wildcard := do
    sort_summands_core tt l none,
    ctx ← local_context,
    ctx.mmap (λ e, sort_summands_core tt l (expr.local_pp_name e)),
    skip
  | loc.ns names := do
    names.mmap $ sort_summands_core ff l,
    skip
  end

end tactic.interactive
