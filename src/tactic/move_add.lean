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
Whenever it finds one, it moves the summands that unify to `a, b, c`, removing all parentheses.

See the doc-string for `tactic.interactive.move_add` for more information.

##  Implementation notes

The implementation of `move_add` only moves the terms specified by the user (and rearranges
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

* Add support for `neg` in additive groups?
* Add different operations other than `+`, most notably `*`?
* Add functionality for moving terms across the two sides of an in/dis/equality.
  E.g. it might be desirable to have `to_lhs [a]` converting `b + c = a + d` to `- a + b + c = d`.
* Add a non-recursive version for use in `conv` mode.
* Revise tests?
-/

namespace tactic

namespace move_add

/--  Given a list `un` of `α`s and a list `bo` of `bool`s, return the sublist of `un`
consisting of the entries of `un` whose corresponding entry in `bo` is `tt`.

Used for error management: `un` is the list of user inputs, `bo` is the list encoding which input
is unused (`tt`) and which input is used (`ff`).
`return_unused` returns the unused user inputs. -/
def return_unused {α : Type*} : list α → list bool → list α
| un [] := un
| [] bo := []
| (u::us) (b::bs) := if b then u::return_unused us bs else return_unused us bs

/--  Given a list `lp` of `bool × pexpr` and a list `sl` of `expr`, scan the elements of `lp` one
at a time and produce 3 sublists of `sl`.

If `(tf,pe)` is the first element of `lp`, we look for the first element of `sl` that unifies with
`pe.to_expr`.  If no such element exists, then we discard `(tf,pe)` and move along.
If `eu ∈ sl` is the first element of `sl` that unifies with `pe.to_expr`, then we add `eu` as the
next element of either the first or the second list, depending on the boolean `tf` and we remove
`eu` from the list `sl`.  In this case, we continue our scanning with the next element of `lp`,
replacing `sl` by `sl.erase eu`.

Once we exhaust the elements of `lp`, we return the three lists:
* first the list of elements of `sl` that came from an element of `lp` whose boolean was `tt`,
* next the list of elements of `sl` that came from an element of `lp` whose boolean was `ff`, and
* finally the ununified elements of `sl`.

The ununified elements of `sl` get used for error management: they keep track of which user inputs
are superfluous. -/
meta def move_left_or_right : list (bool × expr) → list expr → list bool →
  tactic (list expr × list expr × list expr × list bool)
| [] sl is_unused      := return ([], [], sl, is_unused)
| (be::l) sl is_unused :=
  do (ex :: hs) ← sl.mfilter $ λ e', succeeds $ unify be.2 e' |
    move_left_or_right l sl (is_unused.append [tt]),
  (l1, l2, l3, is_unused) ← move_left_or_right l (sl.erase ex) (is_unused.append [ff]),
  if be.1 then return (ex::l1, l2, l3, is_unused) else return (l1, ex::l2, l3, is_unused)

/--  Given a list of pairs `α × pexpr`, we convert it to a list of `α × expr`. -/
meta def snd_to_expr {α : Type*} (lp : list (α × pexpr)) : tactic (list (α × expr)) :=
lp.mmap $ λ x : α × pexpr, do
  e ← to_expr x.2 tt ff,
  return (x.1, e)

/--  We combine `snd_to_expr` and `move_left_or_right`, and then some:
1. we convert a list pairs `bool × pexpr` to a list of pairs `bool × expr`,
2. we use the extra input `sl : list expr` to perform the unification and sorting step
   `move_left_or_right`,
3. we jam the third factor inside the first two.
-/
meta def final_sorting (lp : list (bool × pexpr)) (sl : list expr) :
  tactic (list expr × list bool) :=
do
  lp_exp : list (bool × expr) ← snd_to_expr lp,
  (l1, l2, l3, is_unused) ← move_left_or_right lp_exp sl [],
  return (l1 ++ l3 ++ l2, is_unused)

/-- Partially traverses an expression in search for a sum of terms and producing a list of them.
In the intended application, the `bool` input is initially set to `tt`.
The first time `candidates` finds an expression whose head symbol is `has_add.add`,
`candidates` adds the expression to the list, and recurses inside the summands as well,
but with the boolean set to `ff`.  This prevents partial summands of a large sum to
appear.  Once `candidates` finds a term whose head symbol is not `has_add.add`,
it reverts the boolean to `tt`, so that the recursion can isolate further sums later in the
expression.

For instance, applying `candidates` to `a + (b + c)*(d + e) + f + g` produces
`[a + (b + c) * (d + e) + f + g, b + c, d + e]`. -/
meta def candidates : bool → expr → list expr
| bo e@`(%%a + %%b)              := if bo then [e] ++ candidates ff a ++ candidates ff b
                                    else candidates ff a ++ candidates ff b
| bo (expr.lam _ _ e f)          := candidates tt e ++ candidates tt f
| bo (expr.pi  _ _ e f)          := candidates tt e ++ candidates tt f
| bo (expr.mvar  _ _ e)          := candidates tt e
| bo (expr.app e f)              := candidates tt e ++ candidates tt f
| bo (expr.elet _ e f g)         := candidates tt e ++ candidates tt f ++ candidates tt g
| bo e := []

/-- `sorted_sum` takes an optional location name `hyp` for where it will be applied, a list `ll` of
`bool × pexpr` (arising as the user-provided input to `move_add`) and an expression `e`.

`sorted_sum hyp ll e` returns an ordered sum of the terms of `e`, where the order is
determined using the `final_sorting` applied to `ll` and `e`.

We use this function for expressions in an additive commutative semigroup. -/
meta def sorted_sum (hyp : option name) (ll : list (bool × pexpr)) (e : expr) :
  tactic (list bool) :=
do
  (sli, is_unused) ← final_sorting ll (e.list_summands),
  match sli with
  | []       := return is_unused
  | (eₕ::es) := do
    e' ← es.mfoldl (λ eₗ eᵣ, mk_app `has_add.add [eₗ, eᵣ]) eₕ,
    e_eq ← mk_app `eq [e, e'],
    e_eq_fmt ← pp e_eq,
    h ← solve_aux e_eq $
      reflexivity <|>
      `[{ simp only [add_comm, add_assoc, add_left_comm], done, }] |
      fail format!"failed to prove:\n\n{e_eq_fmt}",
    match hyp with
    | some loc := do
      try $ get_local loc >>= rewrite_hyp h.2,
      pure is_unused
    | none     := do
      try $ rewrite_target h.2,
      pure is_unused
    end
  end

/--  Extracts the "summand expressions" in `e` via `candidates` and, to each one of them, applies
`sorted_sum`.  Besides the state changes, which involve the reordering of the addends,
`is_unused_and_sort` outputs a list of Booleans, encoding which user input was unused
(`tt`) and which one was used (`ff`).  This information is used for reporting unused inputs. -/
meta def is_unused_and_sort (hyp : option name) (ll : list (bool × pexpr)) (e : expr) :
  tactic (list bool) :=
do results ← (candidates tt e).mmap (sorted_sum hyp ll),
  return $ results.transpose.map list.band

/-- Passes the user input `ll` to `is_unused_and_sort` at a single location, that could either be
`none` (referring to the goal) or `some name` (referring to hypothesis `name`).  Returns a pair
consisting of a boolean and a further list of booleans.  The single boolean is `tt` iff the tactic
did *not* change the goal on which it was acting.  The list of booleans records which variable in
`ll` has been unified in the application: `tt` means that the corresponding variable has *not* been
unified.

This definition is useful to streamline error catching. -/
meta def with_errors (ll : list (bool × pexpr)) : option name → tactic (bool × list bool)
| (some hyp) := do
  thyp ← get_local hyp >>= infer_type,
  is_unused ← is_unused_and_sort hyp ll thyp,
  nthyp ← get_local hyp >>= infer_type,
  if thyp = nthyp then return (tt, is_unused) else return (ff, is_unused)
| none       := do
  t ← target,
  is_unused ← is_unused_and_sort none ll t,
  tn ← target,
  if t = tn then return (tt, is_unused) else return (ff, is_unused)

section parsing_arguments_for_move_add

setup_tactic_parser
/-- `move_add_arg` is a single elementary argument that `move_add` takes for the
variables to be moved.  It is either a `pexpr`, or a `pexpr` preceded by a `←`. -/
meta def move_add_arg (prec : nat) : parser (bool × pexpr) :=
prod.mk <$> (option.is_some <$> (tk "<-")?) <*> parser.pexpr prec

/-- `move_pexpr_list_or_texpr` is either a list of `move_add_arg`, possibly empty, or a single
`move_add_arg`. -/
meta def move_pexpr_list_or_texpr : parser (list (bool × pexpr)) :=
list_of (move_add_arg 0) <|> list.ret <$> move_add_arg tac_rbp <|> return []

end parsing_arguments_for_move_add

end move_add

namespace interactive

open move_add
setup_tactic_parser

/--
Calling `move_add [a, ← b, c]`, recursively looks inside the goal for expressions involving a sum.
Whenever it finds one, it moves the summands that unify to `a, b, c`, removing all parentheses.
Repetitions are allowed, and are processed following the user-specified ordering.
The terms preceded by a `←` get placed to the left, the ones without the arrow get placed to the
right.  Unnamed terms stay in place.  Due to re-parenthesizing, doing `move_add` with no argument
may change the goal. Also, the *order* in which the terms are provided matters: the tactic reads
them from left to right.  This is especially important if there are multiple matches for the typed
terms in the given expressions.

A single call of `move_add` moves terms across different sums in the same expression.
Here is an example.

```lean
import tactic.move_add

example {a b c d : ℕ} (h : c = d) : c + b + a = b + a + d :=
begin
  move_add [← a, b],  -- Goal: `a + c + b = a + d + b`  -- both sides changed
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

Finally, `move_add` can also target one or more hypotheses.  If `hp₁, hp₂` are in the
local context, then `move_add [f, ← g] at hp₁ hp₂` performs the rearranging at `hp₁` and `hp₂`.
As usual, passing `⊢` refers to acting on the goal as well.

##  Reporting sub-optimal usage

The tactic could fail to prove the reordering.  One potential cause is when there are multiple
matches for the rearrangements and an earlier rewrite makes a subsequent one fail.  If that is not
the case, though, I would not know what the cause of this could be.

There are three kinds of unwanted use for `move_add` that result in errors: the tactic fails
and flags the unwanted use.
1. `move_add [vars]? at *` reports globally unused variables and whether *all* goals
   are unchanged, not *each unchanged goal*.
2. If a target of `move_add [vars]? at targets` is left unchanged by the tactic, then this will be
   flagged (unless we are using `at *`).
3. If a user-provided expression never unifies, then the variable is flagged.

The tactic produces an error, reporting unused inputs and unchanged targets.

For instance, `move_add ← _` always fails reporting an unchanged goal, but never an unused variable.

##  Comparison with existing tactics

* `tactive.interactive.abel`
  performs a "reduction to normal form" that allows it to close goals involving sums with higher
  success rate than `move_add`.  If the goal is an equality of two sums that are simply obtained by
  reparenthesizing and permuting summands, then `move_add [appropriate terms]` can close the goal.
  Compared to `abel`, `move_add` has the advantage of allowing the user to specify the beginning and
  the end of the final sum, so that from there the user can continue with the proof.

* `tactic.interactive.ac_change`
  supports a wide variety of operations.  At the moment, `move_add` only works with addition.
  Still, on several experiments, `move_add` had a much quicker performance than `ac_change`.
  Also, for `move_add` the user need only specify a few terms: the tactic itself takes care of
  producing the full rearrangement and proving it "behind the scenes".

###  Remark:
It is still possible that the same output of `move_add [exprs]` can be achieved by a proper sublist
of `[exprs]`, even if the tactic does not flag anything.  For instance, giving the full re-ordering
of the expressions in the target that we want to achieve will not complain that there are unused
variables, since all the user-provided variables have been matched.  Of course, specifying the order
of all-but-the-last variable suffices to determine the permutation.  E.g., with a goal of
`a + b = 0`, applying either one of `move_add [b,a]`, or `move_add a`, or `move_add ← b` has the
same effect and changes the goal to `b + a = 0`.  These are all valid uses of `move_add`.
-/
meta def move_add (args : parse move_pexpr_list_or_texpr) (locat : parse location) :
  tactic unit :=
match locat with
| loc.wildcard := do
  ctx ← local_context,
  err_rep ← ctx.mmap (λ e, with_errors args e.local_pp_name),
  er_t ← with_errors args none,
  if ff ∉ er_t.1::err_rep.map (λ e, e.1) then
    fail "'move_add at *' changed nothing" else skip,
  let li_unused := er_t.2::err_rep.map (λ e, e.2),
  let li_unused_clear := li_unused.filter (≠ []),
  let li_tf_vars := li_unused_clear.transpose.map list.band,
  match (return_unused args li_tf_vars).map (λ e : bool × pexpr, e.2) with
  | []   := skip
  | [pe] := fail format!"'{pe}' is an unused variable"
  | pes  := fail format!"'{pes}' are unused variables"
  end,
  assumption <|> try (tactic.reflexivity reducible)
| loc.ns names := do
  err_rep ← names.mmap $ with_errors args,
  let conds := err_rep.map (λ e, e.1),
  linames ← (return_unused names conds).reduce_option.mmap get_local,
  if linames ≠ [] then fail format!"'{linames}' did not change" else skip,
  if none ∈ return_unused names conds then fail "Goal did not change" else skip,
  let li_unused := (err_rep.map (λ e, e.2)),
  let li_unused_clear := li_unused.filter (≠ []),
  let li_tf_vars := li_unused_clear.transpose.map list.band,
  match (return_unused args li_tf_vars).map (λ e : bool × pexpr, e.2) with
  | []   := skip
  | [pe] := fail format!"'{pe}' is an unused variable"
  | pes  := fail format!"'{pes}' are unused variables"
  end,
  assumption <|> try (tactic.reflexivity reducible)
  end

add_tactic_doc
{ name := "move_add",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.move_add],
  tags := ["arithmetic"] }

end interactive
end tactic
