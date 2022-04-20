/-
Copyright (c) 2022 Arthur Paulino, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Damiano Testa
-/
import tactic.core
import data.polynomial.basic

/-!
# `sort_summands`: a tactic for sorting sums

Calling `sort_summands`, recursively looks inside the goal for expressions involving a sum.
Whenever it finds one, it sorts its terms, removing all parentheses.

`sort_summands` allows the use control over which summands should appear first and which ones
should appear last in the rearranged expression.  Here is an example.


Right now, the heuristic
is somewhat crude: if an individual summand is of the exact form `monomial n r`, with `n` a numeral,
then `monomial n r` moves to the right of the sum and this segment is sorted by increasing value of
`n`.  The remaining terms appear at the beginning of the sum and are sorted alphabetically.

```lean
example (hp : f = g) :
  7 + f + (C r * X ^ 3 + 42) + X ^ 5 * h = C r * X ^ 3 + h * X ^ 5 + g + 7 + 42 :=
begin
  -- we move `f, g` to the right of their respective sides, so `congr` helps us remove the
  -- repeated term
  sort_summands [f, g],
  congr' 2, -- takes care of using assumption `hp`
  exact X_pow_mul,
end
```

To allow for more flexibility, `sort_summands` takes an optional argument that can be either a
single term or a list of terms.  Calling `sort_summands f` or `sort_summands [f,.., g]` performs the
sorting, except that the explicitly given terms appear last in the final sum (repetitions and
inexistent terms are ignored).

Finally, `sort_summands` can also be targeted to a hypothesis.  If `hp` is in the local context,
then `sort_summands [f, g] at hp` performs the rearranging at `hp`.


##  Future work

To add better heuristics, an easy approach is to change the definition of `compare_fn`.
Right now, it simply does a case-split: we compare two expressions alphabetically, unless they are
both `monomial <deg> <coeff>`, in which case, we place the term last and we use `<deg>` to further
compare.

* Allow for pattern-matching in the list of terms?
* Allow to pass `[f, ←g, h, ←i]` to mean that `f, h` come last and `g i` come first?
* Improve sorting heuristic?
* Add support for `neg` and additive groups?
* Allow the option of not changing the given order, except for the explicitly listed terms?
  E.g. `sort_summands only [f, g]`, extracts `f` and `g`, placing them last, but leaving the rest
  unchanged (except for the parenthesis, which will be straightened).
* Add optional different operations than `+`, most notably `*`?
* Allow custom ordering?  E.g. `sort_summands using my_rel`, where `my_rel : N → N → Prop` is a
  relation on a type (with `+`), and, if `sort_summands` encounters a sum of terms of type `N`,
  then it will ask the user to prove the required sorting.
* Add more tests.
-/

/--  We sort the elements of the list `l`, making sure that the elements of `t` appear at the
end of the list.

Use as `l.sort_with_top t rel`.
 -/
def list.sort_with_top {N : Type*} [decidable_eq N] (l t : list N) (rel : N → N → bool) :
  list N :=
let tl := t.dedup.filter (∈ l) in (l.filter (∉ tl)).qsort rel ++ tl

/--  Mimics closely `list.partition`, except that it uses the first factor as the partitioning
condition and passes on the second factors to the partitions. -/
def list.split_factors {α : Type*} (l : list (bool × α)) : list α × list α :=
(l.partition (λ i : bool × α, i.1)).map (list.map (λ i, i.2)) (list.map (λ i, i.2))


/--  Let `ll = (il,fl)` be a pair of `list N`.  We sort the elements of the list `l : list N`,
using a relation `rel : N → N → bool`, overriding it as needed to make sure that the elements of
the list `il` are initial and the elements of `fl` are final in the sorted list.

Use as `l.sort_with_ends ll rel`.
 -/
def list.sort_with_ends {N : Type*} [decidable_eq N] (l : list N) (ll : list N × list N)
  (rel : N → N → bool) :
  list N :=
-- the list of initial elements
let il := ll.1.dedup.filter (∈ l) in
-- the list of final elements
let fl := (ll.2.dedup.filter (∈ l)).filter (∉ il) in
il ++ ((l.filter (∉ il ++ fl)).qsort rel) ++ fl

namespace tactic

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

namespace interactive

open tactic
setup_tactic_parser

/--  Takes an `expr` and returns a list of its summands. -/
meta def get_summands : expr → list expr
| `(%%a + %%b) := get_summands a ++ get_summands b
| a            := [a]

section with_rel

/--  Let `rel : expr → expr → bool` be a relation, `ll = (il,fl)` a pair of lists of expressions
and `e` an expression.
`sorted_sum_with_rel rel t e` returns an ordered sum of the terms of `e`, where the order is
determined using the relation `rel`, except that the elements from the list `il`
appear first and the elements of the list `fl` appear last (duplicates are ignored, overlaps
between `il` and `fl` are removed from `fl`).

We use this function for expressions in an additive commutative semigroup. -/
meta def sorted_sum_with_rel
  (hyp : option name) (rel : expr → expr → bool) (ll : list expr × list expr) (e : expr) :
  tactic unit :=
match (get_summands e).sort_with_ends ll rel with
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
meta def recurse_on_expr
  (ll : list expr × list expr) (hyp : option name) (rel : expr → expr → bool) :
  expr → tactic unit
| e@`(%%_ + %%_)     := sorted_sum_with_rel hyp rel ll e
| (expr.lam _ _ _ e) := recurse_on_expr e
| (expr.pi  _ _ _ e) := recurse_on_expr e
| e                  := e.get_app_args.mmap' recurse_on_expr

/-- Calls `recurse_on_expr` with the right expression, depending on the tactic location. -/
meta def sort_summands_aux (rel : expr → expr → bool) (ll : list expr × list expr) :
  option name → tactic unit
| (some hyp) := get_local hyp >>= infer_type >>= recurse_on_expr ll hyp rel
| none       := target >>= recurse_on_expr ll none rel

end with_rel

/--  A version of `sort_summands_aux` that allows failure, if `allow_failure = tt`. -/
meta def sort_summands_core
  (allow_failure : bool) (ll : list expr × list expr) (hyp : option name) :
  tactic unit :=
if allow_failure then sort_summands_aux compare_fn ll hyp <|> skip
else sort_summands_aux compare_fn ll hyp

/-- `sort_summands_arg` is a single elementary argument that `sort_summands` takes for the
variables to be sorted.  It is either a `pexpr`, or a `pexpr` preceded by a `←`. -/
meta def sort_summands_arg (prec : nat) : lean.parser (bool × pexpr) :=
prod.mk <$> (option.is_some <$> (tk "<-")?) <*> parser.pexpr prec

/-- `sort_pexpr_list_or_texpr` is either a list of `sort_summands`, possible empty, or a single
`sort_summand_arg`. -/
meta def sort_pexpr_list_or_texpr := list_of (sort_summands_arg 0) <|>
    list.ret <$> (sort_summands_arg tac_rbp) <|>
    return []

meta def split_sort_args
  (args : parse (
    list_of (sort_summands_arg 0) <|>
    list.ret <$> (sort_summands_arg tac_rbp) <|>
    return [])) : tactic unit :=
trace $ list.split_factors args

/--
Calling `sort_summands`, recursively looks inside the goal for expressions involving a sum.
Whenever it finds one, it sorts its terms following a heuristic.  Right now, the heuristic
is somewhat crude: if an individual summand is of the exact form `monomial n r`, with `n` a numeral,
then `monomial n r` moves to the right of the sum and this segment is sorted by increasing value of
`n`.  The remaining terms appear at the beginning of the sum and are sorted alphabetically.

```lean
example {f g : R[X]} {a b : R} (h : f + g + monomial 5 a + monomial 7 b = 0) :
  (f + monomial 5 a) + (monomial 7 b + g) = 0 :=
begin
  sort_summands,
  assumption,
end
```

To allow for more flexibility, `sort_summands` takes an optional argument that can be either a
single term or a list of terms.  Calling `sort_summands f` or `sort_summands [f,.., g]` performs the
sorting, except that the explicitly given terms appear last in the final sum (repetitions and
inexistent terms are ignored).

Finally, `sort_summands` can also be targeted to a hypothesis.  If `hp` is in the local context,
`sort_summands [f, g] at hp` performs the rearranging at `hp`.
-/
meta def sort_summands (args : parse sort_pexpr_list_or_texpr)
 (locat : parse location)
  : tactic unit :=
do
  let ll := args.split_factors,
  il ← ll.1.mmap to_expr,
  fl ← ll.2.mmap to_expr,
  match locat with
  | loc.wildcard := do
    sort_summands_core tt (il,fl) none,
    ctx ← local_context,
    ctx.mmap (λ e, sort_summands_core tt (il,fl) (expr.local_pp_name e)),
    skip
  | loc.ns names := do
    names.mmap $ sort_summands_core ff (il,fl),
    skip
    end

add_tactic_doc
{ name := "sort_summands",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.sort_summands],
  tags := ["arithmetic"] }

end interactive

end tactic
