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

This file defines a general `move_op` tactic, intended for reordering terms in an expression
obtained by repeated applications of a given associative, commutative binary operation.  The
user decides the final reordering.  Applying `move_op` without specifying the order will simply
remove all parentheses from the expression.
The main user-facing tactics are `move_add` and `move_mul`, dealing with addition and
multiplication, respectively.

In what is below, we talk about `move_add` for definiteness, but everything applies
to `move_mul` and to the more general `move_op`.

The implementation of `move_add` only moves the terms specified by the user (and rearranges
parentheses).

Note that the tactic `abel` already implements a very solid heuristic for normalizing terms in an
additive commutative semigroup and produces expressions in more or less standard form.
The scope of `move_add` is different: it is designed to make it easy to move individual terms
around a sum.

##  Future work

* Add support for `neg/div/inv` in additive/multiplicative groups?
* Customize error messages to mention `move_add/move_mul` instead of `move_op`?
* Add different operations other than `+` and `*`?  E.g. `∪, ∩, ⊓, ⊔, ...`?
  Should there be the desire for supporting more operations, it might make sense to extract
  the `simp [add] <|> simp [mul]` block in `with_errors` to a separate tactic,
  including all the lemmas used for the rearrangement to work.
* Add functionality for moving terms across the two sides of an in/dis/equality.
  E.g. it might be desirable to have `to_lhs [a]` converting `b + c = a + d` to `- a + b + c = d`.
* Add a non-recursive version for use in `conv` mode.
* Revise tests?
-/

namespace tactic

namespace move_op

/-!
Throughout this file, `op : pexpr` denotes an arbitrary (binary) operation.  We do not use,
but implicitly imagine, that this operation is associative, since we extract iterations of
such operations, with complete disregard of the order in which these iterations arise.
-/

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
| (be::l) sl is_unused := do
    (ex :: _) ← sl.mfilter $ λ e', succeeds $ unify be.2 e' |
    move_left_or_right l sl (is_unused.append [tt]),
  (l1, l2, l3, is_unused) ← move_left_or_right l (sl.erase ex) (is_unused.append [ff]),
  if be.1 then return (ex::l1, l2, l3, is_unused) else return (l1, ex::l2, l3, is_unused)

/--  We adapt `move_left_or_right` to our goal:
1. we convert a list of pairs `bool × pexpr` to a list of pairs `bool × expr`,
2. we use the extra input `sl : list expr` to perform the unification and sorting step
   `move_left_or_right`,
3. we jam the third factor inside the first two.
-/
meta def final_sort (lp : list (bool × pexpr)) (sl : list expr) : tactic (list expr × list bool) :=
do
  lp_exp : list (bool × expr) ← lp.mmap $ λ x, (do e ← to_expr x.2 tt ff, return (x.1, e)),
  (l1, l2, l3, is_unused) ← move_left_or_right lp_exp sl [],
  return (l1 ++ l3 ++ l2, is_unused)

/-- `is_given_op op e` checks if the head term of `e` is the binary operation `op`, returning
`tt` if this is the case and `ff` otherwise. -/
meta def is_given_op (op : expr) : expr → tactic bool
| (expr.app (expr.app F a) b) := succeeds $ unify op F
| _ := return ff

/-- `reorder_oper op lp boos e` converts an expression `e` to a similar looking one.
The tactic scans the expression `e` looking for subexpressions that begin with the given binary
operation `op`.  As soon as `reorder_oper` finds one such subexpression,
* it extracts the "`op`-summands" in the subexpression,
* it rearranges them according to the rules determined by `lp`,
* it recurses into each `op`-summand.

The `boos` parameter is a list of booleans.  It is keeping track of which of the inputs provided
by `lp` is actually used to perform the rearrangements.  It is useful to report unused inputs.
In its intended application, it is set to a list of `tt`, one for each element of `lp`, indicating
that they all begin unused.

Here are two examples:
```lean
#eval trace $ reorder_oper ``((=)) [(ff,``(2)), (tt,``(7))] [tt] `(∀ x y : ℕ, 2 = 0)
--  (ℕ → ℕ → 0 = 2, [ff, tt])
-- the input `[(ff,``(2)), (tt,``(7))]` instructs Lean to move `2` to the right and `7`
-- to the right.  Lean reports that `2` is not unused and `7` is unused as `[ff, tt]`.

#eval trace $ reorder_oper ``((+)) [(ff,``(2)), (tt,``(5))] [tt, tt]
  `(λ (e : ℕ), ∀ (x : ℕ), ∃ (y : ℕ),
      2 + x * (y + (e + 5)) + y = x + 2 + e → 2 + x = x + 5 + (2 + y))
/-  `2` moves to the right, `5` moves to the left.  Lean reports that `2, 5` are not unused
    as `[ff,ff]`
   (λ (e : ℕ), ∀ (x : ℕ), ∃ (y : ℕ),
      x * (5 + y + e) + y + 2   = x + e + 2 → x + 2 = 5 + x + y + 2, [ff, ff]) -/
```
-/
meta def reorder_oper (op : pexpr) (lp : list (bool × pexpr)) :
  list bool → expr → tactic (expr × list bool)
| lu F'@(expr.app F b) := do
  op ← to_expr op tt ff,
  cond ← is_given_op op F',
  if cond then do
    (sort_list, is_unused) ← list_binary_operands op F' >>= final_sort lp,
    sort_all ← sort_list.mmap $ reorder_oper ([lu, is_unused].transpose.map list.band),
    let (recs, list_unused) := sort_all.unzip,
    let summed := (recs.drop 1).foldl (λ e f, op.mk_app [e, f]) ((recs.nth 0).get_or_else `(0)),
    return (summed, list_unused.transpose.map list.band)
  else do
    [(Fn, unused_F), (bn, unused_b)] ← [F, b].mmap $ reorder_oper lu,
    return $ (expr.app Fn bn, [unused_F, unused_b, lu].transpose.map list.band)
| lu (expr.pi na bi e f)           := do [en, fn] ← [e, f].mmap $ reorder_oper lu,
    return (expr.pi  na bi en.1 fn.1, [en.2, fn.2].transpose.map list.band)
| lu (expr.lam na bi e f)          := do [en, fn] ← [e, f].mmap $ reorder_oper lu,
    return (expr.lam na bi en.1 fn.1, [en.2, fn.2].transpose.map list.band)
| lu (expr.mvar na pp e)           := do en ← reorder_oper lu e,
  return (expr.mvar na pp en.1, [en.2].transpose.map list.band)
| lu (expr.local_const na pp bi e) := do en ← reorder_oper lu e,
  return (expr.local_const na pp bi en.1, [en.2].transpose.map list.band)
| lu (expr.elet na e f g)          := do [en, fn, gn] ← [e, f, g].mmap $ reorder_oper lu,
  return (expr.elet na en.1 fn.1 gn.1, [en.2, fn.2, gn.2].transpose.map list.band)
| lu (expr.macro ma le)            := do len ← le.mmap $ reorder_oper lu,
  let (lee, lb) := len.unzip,
  return (expr.macro ma lee, lb.transpose.map list.band)
| lu e := pure (e, lu)

/-- Parses the user input `na` to `reorder_oper` at a single location, that could either be
`none` (referring to the goal) or `some name` (referring to hypothesis `name`).  Replaces the
given location by the rearranged one that `with_errors` receives from `reorder_oper`.
Returns a pair consisting of a boolean and a further list of booleans.
The single boolean is `tt` iff the tactic did *not* change the goal on which it was acting.
The list of booleans records which variable in `ll` has been unified in the application:
`tt` means that the corresponding variable has *not* been unified.

This definition is useful to streamline error catching. -/
meta def with_errors (op : pexpr) (lp : list (bool × pexpr)) (na : option name) :
  tactic (bool × list bool) :=
do (thyp, hyploc) ←  -- `hyploc` is only meaningful in the "is some/else" branch
  if na.is_none then do t ← target, return (t, t)
  else
  (do nn ← get_unused_name,
      hl ← get_local (na.get_or_else nn),
      th ← infer_type hl,
      return (th, hl)),
  (reordered, is_unused) ← reorder_oper op lp (lp.map (λ _, tt)) thyp,
  unify reordered thyp >> return (tt, is_unused) <|> do
  -- the current `do` block takes place where the reordered expression is not equal to the original
  neq ← mk_app `eq [thyp, reordered],
  pre ← pp reordered,
  (_, prf) ← solve_aux neq $
    `[{ simp only [add_comm, add_assoc, add_left_comm], done }] <|>
    `[{ simp only [mul_comm, mul_assoc, mul_left_comm], done }] <|>
    fail format!("the associative/commutative lemmas used do not suffice to prove that " ++
    "the initial goal equals:\n\n{pre}\n"),
  if na.is_none then refine ``(eq.mpr %%prf _) else replace_hyp hyploc reordered prf >> skip,
  return (ff, is_unused)

section parsing_arguments_for_move_op
setup_tactic_parser

/-- `move_op_arg` is a single elementary argument that `move_op` takes for the
variables to be moved.  It is either a `pexpr`, or a `pexpr` preceded by a `←`. -/
meta def move_op_arg (prec : nat) : parser (bool × pexpr) :=
prod.mk <$> (option.is_some <$> (tk "<-")?) <*> parser.pexpr prec

/-- `move_pexpr_list_or_texpr` is either a list of `move_op_arg`, possibly empty, or a single
`move_op_arg`. -/
meta def move_pexpr_list_or_texpr : parser (list (bool × pexpr)) :=
list_of (move_op_arg 0) <|> list.ret <$> move_op_arg tac_rbp <|> return []

end parsing_arguments_for_move_op

end move_op

setup_tactic_parser
open move_op

/--  `move_op args locat op` is the non-interactive version of the main tactics `move_add` and
`move_mul` of this file.  Given as input `args` (a list of terms of a sequence of operands),
`locat` (hypotheses or goal where the tactic should act) and `op` (the operation to use),
`move_op` attempts to perform the rearrangement of the terms determined by `args`.

Currently, the tactic uses only `add/mul_comm, add/mul_assoc, add/mul_left_comm`, so other
operations will not actually work.
-/
meta def move_op (args : parse move_pexpr_list_or_texpr) (locat : parse location) (op : pexpr) :
  tactic unit := do
locas ← locat.get_locals,
tg ← target,
let locas_with_tg := if locat.include_goal then locas ++ [tg] else locas,
ner ← locas_with_tg.mmap (λ e, with_errors op args e.local_pp_name <|> with_errors op args none),
let (unch_tgts, unus_vars) := ner.unzip,
let str_unva := match
  (return_unused args (unus_vars.transpose.map list.band)).map (λ e : bool × pexpr, e.2) with
  | []   := ""
  | [pe] := "'" ++ to_string pe ++"' is an unused variable"
  | pes  := "'" ++ to_string pes ++"' are unused variables"
  end,
let str_tgts := match locat with
  | loc.wildcard := if unch_tgts.band then "'move_op at *' changed nothing" else ""
  | loc.ns names := let linames := return_unused locas unch_tgts in
      (if none ∈ return_unused names unch_tgts then "Goal did not change\n" else "") ++
      (if linames ≠ [] then ("'" ++ to_string linames.reverse ++ "' did not change") else "")
  end,
guard (str_tgts ++ str_unva = "") <|>
  fail (if str_tgts.length = 0 then str_unva else str_tgts ++ "\n" ++ str_unva),
assumption <|> try (tactic.reflexivity reducible)

namespace interactive

/--
Calling `move_add [a, ← b, c]`, recursively looks inside the goal for expressions involving a sum.
Whenever it finds one, it moves the summands that unify to `a, b, c`, removing all parentheses.
Repetitions are allowed, and are processed following the user-specified ordering.
The terms preceded by a `←` get placed to the left, the ones without the arrow get placed to the
right.  Unnamed terms stay in place.  Due to re-parenthesizing, doing `move_add` with no argument
may change the goal. Also, the *order* in which the terms are provided matters: the tactic reads
them from left to right.  This is especially important if there are multiple matches for the typed
terms in the given expressions.

A single call of `move_op` moves terms across different sums in the same expression.
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
move_op args locat ``((+))

/--  See the doc-string for `move_add` and mentally
replace addition with multiplication throughout. ;-) -/
meta def move_mul (args : parse move_pexpr_list_or_texpr) (locat : parse location) :
  tactic unit :=
move_op args locat ``(has_mul.mul)

add_tactic_doc
{ name := "move_add",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.move_add],
  tags := ["arithmetic"] }

add_tactic_doc
{ name := "move_mul",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.move_add],
  tags := ["arithmetic"] }

end interactive
end tactic
