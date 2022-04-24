/-
Copyright (c) 2022 Arthur Paulino, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Damiano Testa
-/
import tactic.core
import algebra.group.basic

/-!
# `move_add`: a tactic for moving summands

Calling `move_add [a, ← b, c]`, recursively looks inside the goal for expressions involving a sum.
Whenever it finds one, it moves the terms `a, b, c`, removing all parentheses.  The terms preceded
by a `←` get placed to the left, the ones without the arrow get placed to the right.  Unnamed terms
stay in place.  Due to re-parenthesizing, doing `move_add` with no argument may change the goal.
Also, the *order* in which the terms are provided matters: the tactic reads them from left to right.
This is especially important if there are multiple matches for the typed terms in the given
expressions.

### Warning:
* The tactic will discard user-provided terms that do not unify with something in the expression.
  This means that the tactic will not give an error if it finds no match of the provided terms.
  The reason for this choice is that we want a single call of `move_add` to move terms across
  different sums in the same expression.  Here is an example.

```lean
import tactic.move_add
import algebra.group.basic

example {a b c d : ℕ} (h : c = d) : c + b + a = b + a + d :=
begin
  move_add [← a, b],  -- Goal: `a + c + b = a + d + b`
  congr,
  exact h
end

example {a b c d : ℕ} (h : c = d) : c + b * c + a * c = a * d + d + b * d :=
begin
  move_add [_ * c, ← _ * c], -- Goal: `a * c + c + b * c = a * d + d + b * d`
  -- the first `_ * c` unifies with `b * c` and moves it to the right
  -- the second `_ * c` unifies with `a * c` and moves it to the left
  congr;
  assumption
end
```

The list of expressions that `move_add` takes is optional and a single expression can be passed
without brackets.  Thus `move_add ← f` and `move_add [← f]` mean the same.

Finally, `move_add` can also be targeted to one or several hypothesis.  If `hp₁, hp₂` are in the
local context, then `move_add [f, ← g] at hp₁ hp₂` performs the rearranging at `hp₁` and `hp₂`.

##  Implementation notes

The implementation of `move_add` only move the terms specified by the user (and rearranges
parentheses).

An earlier version of this tactic also had a relation on `expr` that performed a sorting on the
terms that were not specified by the user.  This is very easy to implement, if desired, but is not
part of this tactic.  We had used the order given by the `≤` on `string` and a small support for
sorting `monomial`s by increasing degree.

Note that the tactic `abel` already implements a very solid heuristic for normalizing terms in an
additive commutative semigroup and produces expressions in more or less standard form.
The scope of `move_add` is different: it is designed to make it easy to move individual terms
around a sum.

##  Future work

* Add support for `neg` and additive groups?
* Add optional different operations than `+`, most notably `*`?
* Add functionality for moving terms across the two sides of an in/dis/equality.
  E.g. it might be desirable to have `to_lhs [a]` that converts `b + c = a + d` to `a + b + c = d`.
* Add more tests.
-/

open tactic

/-
/-- A `tactic expr` that either finds the first entry of `lc` that unifies with `e` or fails. -/
meta def expr.find_in (e : expr) (lc : list expr) : tactic expr :=
do
  pe ← pp e,
  plc ← pp lc,
  h :: _ ← lc.mfilter $ λ e', succeeds $ unify e e' | fail format!"'{pe}' not found in '{plc}'",
  return h
-/

/-- A `tactic (option expr)` that either finds the first entry `f` of `lc` that unifies with `e`
and returns `some f` or returns `none`. -/
meta def expr.find_in2 (e : expr) (lc : list expr) : tactic (option expr) :=
do
  h ← lc.mfilter $ λ e', succeeds $ unify e e',
  match h with
  | [] := none
  | (f::l) := return $ some f
  end <|>
return none

/--  Given a list `lp` of `bool × pexpr` and a list `sl` of `expr`, scan the elements of `lp` one
at a time and produce 3 sublists of `sl`.

If `(tf,pe)` is the first element of `lp`, we look for the first element of `sl` that unifies with
`pe.to_expr`.  If no such element exists, then we discard `(tf,pe)` and move along.
If `eu ∈ sl` is the first element of `sl` that unifies with `pe.to_expr`, then we add `eu` as the
next element of either the first or the second list, depending on the boolean `tf` and we remove
`eu` from the list `sl`.  In this case, we continue our scanning with the next element of `lp`,
replacing `sl` by `sl.erase eu`.

Once we exhausts the elements of `lp`, we return the three lists:
* first the list of elements of `sl` that came from an element of `lp` whose boolean was `tt`,
* next the ununified elements of `sl` and
* finally the elements of `sl` that came from an element of `lp` whose boolean was `ff`.
 -/
meta def list.unify_list :
  list (bool × expr) → list expr → tactic (list expr × list expr × list expr)
| [] sl := return ([], [], sl)
| (be::l) sl := do
  cond ← be.2.find_in2 sl,
  match cond with
  | none := l.unify_list sl
  | some ex := do
    (l1,l2,l3) ← l.unify_list (sl.erase ex),
    if be.1 then return (ex::l1, l2, l3) else return (l1, ex::l2, l3)
    end

/--  Given a list of pairs `bool × pexpr`, we convert it to a list of `bool × expr`. -/
meta def list.convert_to_expr (lp : list (bool × pexpr)) : tactic (list (bool × expr)) :=
do
  -- extract the list of second coordinates, converted to `expr`s
  le2 : list expr ← (lp.map (λ e : bool × pexpr, e.2)).mmap to_expr,
  -- reattach the booleans
  let tle : list (bool × expr) := (lp.map (λ e : bool × pexpr, e.1)).zip le2,
  return tle

/--  We combine the previous steps.
1. we convert a list pairs `bool × pexpr` to a list of pairs `bool × expr`,
2. we use the extra input `sl : list expr` to perform the unification and sorting step
   `list.unify_list`,
3. we jam the  jam the third factor inside the first two.
-/
meta def list.combined (lp : list (bool × pexpr)) (sl : list expr) : tactic (list expr) :=
do
  to_exp : list (bool × expr) ← list.convert_to_expr lp,
  (l1, l2, l3) ← list.unify_list to_exp sl,
  return (l1 ++ l3 ++ l2)

namespace tactic.interactive
setup_tactic_parser

/--  Takes an `expr` and returns a list of its summands. -/
meta def get_summands : expr → list expr
| `(%%a + %%b) := get_summands a ++ get_summands b
| a            := [a]

--review the doc-string
/-- `sorted_sum` takes an optional location name `hyp` for where it will be applied, a list `ll` of
`bool × pexpr` (arising as the user-provided input to `move_add`) and an expression `e`.

`sorted_sum hyp ll e` returns an ordered sum of the terms of `e`, where the order is
determined using the `list.combined` applied to `ll` and `e`.

We use this function for expressions in an additive commutative semigroup. -/
meta def sorted_sum (hyp : option name) (ll : list (bool × pexpr)) (e : expr) : tactic unit :=
do
  sli ← ll.combined (get_summands e),
  match sli with
  | [] := skip
  | (eₕ::es) := do
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
  end

/-- Partially traverses an expression in search for a sum of terms.
When `recurse_on_expr` finds a sum, it sorts it using `sorted_sum`. -/
meta def recurse_on_expr (hyp : option name) (ll : list (bool × pexpr)) : expr → tactic unit
| e@`(%%_ + %%_)     := sorted_sum hyp ll e <|> skip
| (expr.lam _ _ _ e) := recurse_on_expr e
| (expr.pi  _ _ _ e) := recurse_on_expr e
| e                  := e.get_app_args.mmap' recurse_on_expr

/-- Calls `recurse_on_expr` with the right expression, depending on the tactic location. -/
meta def move_add_aux (ll : list (bool × pexpr)) : option name → tactic unit
| (some hyp) := get_local hyp >>= infer_type >>= recurse_on_expr hyp ll
| none       := target >>= recurse_on_expr none ll

/--  A version of `move_add_aux` that allows failure, if `allow_failure = tt`. -/
meta def move_add_core (allow_failure : bool) (ll : list (bool × pexpr)) (hyp : option name) :
  tactic unit :=
if allow_failure then (move_add_aux ll hyp) <|> skip
else move_add_aux ll hyp

/-- `move_add_arg` is a single elementary argument that `move_add` takes for the
variables to be moved.  It is either a `pexpr`, or a `pexpr` preceded by a `←`. -/
meta def move_add_arg (prec : nat) : parser (bool × pexpr) :=
prod.mk <$> (option.is_some <$> (tk "<-")?) <*> parser.pexpr prec

/-- `move_pexpr_list_or_texpr` is either a list of `move_add_arg`, possibly empty, or a single
`move_add_arg`. -/
meta def move_pexpr_list_or_texpr : parser (list (bool × pexpr)) :=
list_of (move_add_arg 0) <|> list.ret <$> (move_add_arg tac_rbp) <|> return []

/--
Calling `move_add [a, ← b, c, ← d]`, recursively looks inside the goal for
expressions involving a sum.  Whenever `move_add` finds a sum, it sorts its terms using
the user input `[a, ← b, c, ← d]`.  With this input, the output would be
```lean
b + d + (sum of terms sorted using the given relation) + a + c.
```
Finally, `move_add` can also target hypotheses. If `hp` is in the local context,
`move_add [← f, g] at hp` performs the rearranging at `hp`.
-/
meta def move_add (args : parse move_pexpr_list_or_texpr) (locat : parse location) :
  tactic unit :=
match locat with
| loc.wildcard := do
  ctx ← local_context,
  ctx.mmap (λ e, move_add_core tt args e.local_pp_name),
  assumption <|> try (tactic.reflexivity reducible)
| loc.ns names := do
  names.mmap $ move_add_core tt args,
  assumption <|> try (tactic.reflexivity reducible)
  end

add_tactic_doc
{ name := "move_add",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.move_add],
  tags := ["arithmetic"] }

end tactic.interactive
