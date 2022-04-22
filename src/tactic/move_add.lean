/-
Copyright (c) 2022 Arthur Paulino, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Damiano Testa
-/
import tactic.core

/-!
# `move_add`: a tactic for moving summands

Calling `move_add [a, ← b, c]`, recursively looks inside the goal for expressions involving a sum.
Whenever it finds one, it moves the terms `a, b, c`, removing all parentheses.  The terms preceded
by a `←` get placed to the left, the ones without the arrow get placed to the right.  Unnamed terms
stay in place.  Due to re-parenthesizing, doing `move_add` with no argument may change the goal.

`move_add` allows the user control over which summands should appear first and which ones
should appear last in the rearranged expression.  Here is an example.

```lean
example (a b c d : ℕ) : a + (b + d) + c = d + a + (b + c) :=
begin
  move_add [a, ← b], --  Goal becomes: b + d + c + a = b + d + c + a
  refl,
end
```

The list of expressions that `move_add` takes is optional and a single expression can be passed
without parentheses.  Thus `move_add ← f`, `move_add [← f]` and `move_add [←f]` all mean the same.

Finally, `move_add` can also be targeted to a hypothesis.  If `hp` is in the local context,
then `move_add [f, ← g] at hp` performs the rearranging at `hp`.

##  Implementation notes

The implementation of `move_add` goes via `move_add_with_rel`, which takes an extra relation
`rel : expr → expr → bool` as a parameter.  `move_add` uses the trivial relation where all pairs
yield true.  The presence of the relation allows, if desired, to extend the tactic to come up with
heuristics with which to sort terms in an expression, relying less on user input.  In fact, this was
the initial motivation for the tactic: given a polynomial, sort its terms by increasing/decreasing
`nat_degree`.  This is no longer in scope for the current implementation of `move_add`, but could
be developped making use of a non-trivial `rel`.

Note that the tactic `abel` already implements a very solid heuristic for normalizing terms in an
additive commutative semigroup and produces expressions in more or less standard form.
The scope of `move_add` is different: it is designed to make it easy to move individual terms
around a sum.

##  Future work

* Allow for pattern-matching in the list of terms?
* Add support for `neg` and additive groups?
* Add optional different operations than `+`, most notably `*`?
* Add functionality for moving terms across the two sides of an in/dis/equality.
* Add more tests.
-/

/--  Mimics closely `list.partition`, except that it uses the first factor as the partitioning
condition and passes on the second factors to the partitions. -/
def list.split_factors {α : Type*} (l : list (bool × α)) : list α × list α :=
(l.partition (λ i : bool × α, i.1)).map (list.map (λ i, i.2)) (list.map (λ i, i.2))

/--  Let `ll = (il,fl)` be a pair of `list N` and let `l` be a further list of terms from `N`.
We move the elements of the list `l : list N`, using a relation `rel : N → N → bool`, overriding
it as needed to make sure that the elements of the list `il` are initial and the elements of `fl`
are final in the sorted list.

Use as `l.sort_with_ends ll rel`.
 -/
def list.sort_with_ends {N : Type*} [decidable_eq N] (l : list N) (ll : list N × list N)
  (rel : N → N → bool) :
  list N :=
-- the list of initial elements
let il := ll.1.filter (∈ l) in
-- the list of final elements
let fl := ll.2.filter (∈ l) in
il ++ ((l.diff (il ++ fl)).qsort rel) ++ fl

namespace tactic.interactive
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
appear first and the elements of the list `fl` appear last.  Duplicates and overlaps between `il`
and `fl` are *maintained*, since the same term may appear multiple times in the expression.
The only pre-processing that we do to the lists is that we ignore terms of either one of the two
lists in `ll` that do not appear in `get_summands e`.

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
      fail format!"failed to prove:\n\n{e_eq_fmt}",
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
  (ll : list expr × list expr) (hyp : option name) (rel : expr → expr → bool) : expr → tactic unit
| e@`(%%_ + %%_)     := sorted_sum_with_rel hyp rel ll e
| (expr.lam _ _ _ e) := recurse_on_expr e
| (expr.pi  _ _ _ e) := recurse_on_expr e
| e                  := e.get_app_args.mmap' recurse_on_expr

/-- Calls `recurse_on_expr` with the right expression, depending on the tactic location. -/
meta def move_add_aux (rel : expr → expr → bool) (ll : list expr × list expr) :
  option name → tactic unit
| (some hyp) := get_local hyp >>= infer_type >>= recurse_on_expr ll hyp rel
| none       := target >>= recurse_on_expr ll none rel

end with_rel

/--  A version of `move_add_aux` that allows failure, if `allow_failure = tt`. -/
meta def move_add_core (allow_failure : bool) (rel : expr → expr → bool)
  (ll : list expr × list expr) (hyp : option name) :
  tactic unit :=
if allow_failure then move_add_aux rel ll hyp <|> skip
else move_add_aux rel ll hyp

/-- `move_add_arg` is a single elementary argument that `move_add` takes for the
variables to be moved.  It is either a `pexpr`, or a `pexpr` preceded by a `←`. -/
meta def move_add_arg (prec : nat) : lean.parser (bool × pexpr) :=
prod.mk <$> (option.is_some <$> (tk "<-")?) <*> parser.pexpr prec

/-- `move_pexpr_list_or_texpr` is either a list of `move_add_arg`, possibly empty, or a single
`move_add_arg`. -/
meta def move_pexpr_list_or_texpr : lean.parser (list (bool × pexpr)) :=
list_of (move_add_arg 0) <|> list.ret <$> (move_add_arg tac_rbp) <|> return []

/--
Let `rel : expr → expr → bool` be a relation on `expr`s.
Calling `move_add_with_rel rel [a, ← b, c, ← d]`, recursively looks inside the goal for
expressions involving a sum.  Whenever `move_add_with_rel` finds a sum, it sorts its terms using
the relation `rel` and the user input `[a, ← b, c, ← d]`.  With this input, the output would be
```lean
b + d + (sum of terms sorted using the given relation) + a + c.
```
Note that the relation `rel` is a relation on `expr`s.  As such, it can only be used in
`meta`-world.

Finally, `move_add_with_rel` can also target hypotheses. If `hp` is in the local context,
`move_add_with_rel [← f, g] at hp` performs the rearranging at `hp`.
-/
meta def move_add_with_rel
  (rel : expr → expr → bool) (args : parse move_pexpr_list_or_texpr) (locat : parse location) :
  tactic unit :=
do
  let ll := args.split_factors,
  il ← ll.1.mmap to_expr,
  fl ← ll.2.mmap to_expr,
  let ll := (il, fl),
  match locat with
  | loc.wildcard := do
    move_add_core tt rel ll none,
    ctx ← local_context,
    ctx.mmap (λ e, move_add_core tt rel ll e.local_pp_name),
    assumption <|> try (tactic.reflexivity reducible)
  | loc.ns names := do
    names.mmap $ move_add_core ff rel ll,
    assumption <|> try (tactic.reflexivity reducible)
  end
--  in `assumption`, there is a
#check find_same_type
/--
Calling `move_add [a, ← b, c]`, recursively looks inside the goal for expressions involving a sum.
Whenever `move_add` finds a sum, it lists all its summands, moves the terms `a, b, c` as specified,
and removes all parentheses.  The terms preceded by a `←` get placed to the left, the ones without
the arrow get placed to the right.  Unnamed terms stay in place.  Due to re-parenthesizing, doing
`move_add` with no argument may change the goal.

Here is an example.

```lean
example (a b c d : ℕ) : a + (b + d) + c = d + a + (b + c) :=
begin
  move_add [a, ← b], --  Goal becomes: b + d + c + a = b + d + c + a
  refl,
end
```

The list of expressions that `move_add` takes is optional and a single expression can be passed
without parentheses.  Thus `move_add ← f`, `move_add [← f]` and `move_add [←f]` all mean the same.

Finally, `move_add` can also be targeted to one or more hypothesis.  If `hp` is in the local
context, then `move_add [← f, g] at hp` performs the rearranging at `hp`. -/
meta def move_add (args : parse move_pexpr_list_or_texpr) (locat : parse location) :
  tactic unit :=
move_add_with_rel (λ e f, tt) args locat

add_tactic_doc
{ name := "move_add",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.move_add],
  tags := ["arithmetic"] }

end tactic.interactive
