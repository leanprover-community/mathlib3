/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.fintype.basic
import tactic.norm_num

/-!
# Case bash

This file provides the tactic `fin_cases`. `fin_cases x` performs case analysis on `x`, that is
creates one goal for each possible value of `x`, where either:
* `x : α`, where `[fintype α]`
* `x ∈ A`, where `A : finset α`, `A : multiset α` or `A : list α`.
-/

namespace tactic

open expr
open conv.interactive

/-- Checks that the expression looks like `x ∈ A` for `A : finset α`, `multiset α` or `A : list α`,
    and returns the type α. -/
meta def guard_mem_fin (e : expr) : tactic expr :=
do t ← infer_type e,
   α ← mk_mvar,
   to_expr ``(_ ∈ (_ : finset %%α))   tt ff >>= unify t <|>
   to_expr ``(_ ∈ (_ : multiset %%α)) tt ff >>= unify t <|>
   to_expr ``(_ ∈ (_ : list %%α))     tt ff >>= unify t,
   instantiate_mvars α

/--
`expr_list_to_list_expr` converts an `expr` of type `list α`
to a list of `expr`s each with type `α`.

TODO: this should be moved, and possibly duplicates an existing definition.
-/
meta def expr_list_to_list_expr : Π (e : expr), tactic (list expr)
| `(list.cons %%h %%t) := list.cons h <$> expr_list_to_list_expr t
| `([]) := return []
| _ := failed

private meta def fin_cases_at_aux : Π (with_list : list expr) (e : expr), tactic unit
| with_list e :=
(do
  result ← cases_core e,
  match result with
  -- We have a goal with an equation `s`, and a second goal with a smaller `e : x ∈ _`.
  | [(_, [s], _), (_, [e], _)] :=
    do let sn := local_pp_name s,
        ng ← num_goals,
        -- tidy up the new value
        match with_list.nth 0 with
        -- If an explicit value was specified via the `with` keyword, use that.
        | (some h) := tactic.interactive.conv (some sn) none
                        (to_rhs >> conv.interactive.change (to_pexpr h))
        -- Otherwise, call `norm_num`. We let `norm_num` unfold `max` and `min`
        -- because it's helpful for the `interval_cases` tactic.
        | _ := try $ tactic.interactive.conv (some sn) none $
               to_rhs >> conv.interactive.norm_num
                 [simp_arg_type.expr ``(max_def), simp_arg_type.expr ``(min_def)]
        end,
        s ← get_local sn,
        try `[subst %%s],
        ng' ← num_goals,
        when (ng = ng') (rotate_left 1),
        fin_cases_at_aux with_list.tail e
  -- No cases; we're done.
  | [] := skip
  | _ := failed
  end)

/--
`fin_cases_at with_list e` performs case analysis on `e : α`, where `α` is a fintype.
The optional list of expressions `with_list` provides descriptions for the cases of `e`,
for example, to display nats as `n.succ` instead of `n+1`.
These should be defeq to and in the same order as the terms in the enumeration of `α`.
-/
meta def fin_cases_at (nm : option name) : Π (with_list : option pexpr) (e : expr), tactic unit
| with_list e :=
do ty ← try_core $ guard_mem_fin e,
    match ty with
    | none := -- Deal with `x : A`, where `[fintype A]` is available:
      (do
        ty ← infer_type e,
        i ← to_expr ``(fintype %%ty) >>= mk_instance <|> fail "Failed to find `fintype` instance.",
        t ← to_expr ``(%%e ∈ @fintype.elems %%ty %%i),
        v ← to_expr ``(@fintype.complete %%ty %%i %%e),
        h ← assertv (nm.get_or_else `this) t v,
        fin_cases_at with_list h)
    | (some ty) := -- Deal with `x ∈ A` hypotheses:
      (do
        with_list ← match with_list with
        | (some e) := do e ← to_expr ``(%%e : list %%ty), expr_list_to_list_expr e
        | none := return []
        end,
        fin_cases_at_aux with_list e)
    end

namespace interactive

setup_tactic_parser
private meta def hyp := tk "*" *> return none <|> some <$> ident

/--
`fin_cases h` performs case analysis on a hypothesis of the form
`h : A`, where `[fintype A]` is available, or
`h : a ∈ A`, where `A : finset X`, `A : multiset X` or `A : list X`.

`fin_cases *` performs case analysis on all suitable hypotheses.

As an example, in
```
example (f : ℕ → Prop) (p : fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val :=
begin
  fin_cases *; simp,
  all_goals { assumption }
end
```
after `fin_cases p; simp`, there are three goals, `f 0`, `f 1`, and `f 2`.

`fin_cases h with l` takes a list of descriptions for the cases of `h`.
These should be definitionally equal to and in the same order as the
default enumeration of the cases.

For example,
```
example (x y : ℕ) (h : x ∈ [1, 2]) : x = y :=
begin
  fin_cases h with [1, 1+1],
end
```
produces two cases: `1 = y` and `1 + 1 = y`.

When using `fin_cases a` on data `a` defined with `let`,
the tactic will not be able to clear the variable `a`,
and will instead produce hypotheses `this : a = ...`.
These hypotheses can be given a name using `fin_cases a using ha`.

For example,
```
example (f : ℕ → fin 3) : true :=
begin
  let a := f 3,
  fin_cases a using ha,
end
```
produces three goals with hypotheses
`ha : a = 0`, `ha : a = 1`, and `ha : a = 2`.
-/
meta def fin_cases :
  parse hyp → parse (tk "with" *> texpr)? → parse (tk "using" *> ident)? → tactic unit
| none none nm := focus1 $ do
    ctx ← local_context,
    ctx.mfirst (fin_cases_at nm none) <|>
      fail ("No hypothesis of the forms `x ∈ A`, where " ++
        "`A : finset X`, `A : list X`, or `A : multiset X`, or `x : A`, with `[fintype A]`.")
| none (some _) _ := fail "Specify a single hypothesis when using a `with` argument."
| (some n) with_list nm :=
  do
    h ← get_local n,
    focus1 $ fin_cases_at nm with_list h

end interactive

add_tactic_doc
{ name       := "fin_cases",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.fin_cases],
  tags       := ["case bashing"] }

end tactic
