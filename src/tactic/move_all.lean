/-
Copyright (c) 2022 Arthur Paulino, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Damiano Testa
-/
import tactic.move_add
import data.polynomial.basic

/-!
# `move_all`: a tactic for moving summands

Calling `move_all`, recursively looks inside the goal for expressions involving a sum.
Whenever it finds one, it moves its terms, removing all parentheses.

`move_all` allows the use control over which summands should appear first and which ones
should appear last in the rearranged expression.  Here is an example.
###  Rethink example

Right now, the heuristic is somewhat crude: if an individual summand is of the exact form
`monomial n r`, with `n` a numeral, then `monomial n r` moves to the right of the sum and this
segment is sorted by increasing value of `n`.  The remaining terms appear at the beginning of the
sum and are sorted alphabetically.

```lean
example (hp : f = g) :
  7 + f + (C r * X ^ 3 + 42) + X ^ 5 * h = C r * X ^ 3 + h * X ^ 5 + g + 7 + 42 :=
begin
  -- we move `f, g` to the right of their respective sides, so `congr` helps us remove the
  -- repeated term
  sort_summands [f, g],
  congr' 2, -- also takes care of using assumption `hp`
  exact X_pow_mul,
end
```

To allow for more flexibility, `move_all` takes an optional argument that can be either a
single term or a list of terms.  Calling `move_all f` or `move_all [f,.., g]` performs the
sorting, except that the explicitly given terms appear last in the final sum (repetitions and
inexistent terms are ignored).

Finally, `move_all` can also be targeted to a hypothesis.  If `hp` is in the local context,
then `move_all [f, g] at hp` performs the rearranging at `hp`.


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

namespace tactic.interactive
open tactic
setup_tactic_parser

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

meta def move_all (args : parse move_pexpr_list_or_texpr) (locat : parse location) :
  tactic unit :=
move_add_with_rel compare_fn args locat

end tactic.interactive
