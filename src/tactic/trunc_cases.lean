/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.chain
import data.quot

namespace tactic

/-- Auxiliary tactic for `trunc_cases`. -/
private meta def trunc_cases_subsingleton (e : expr) (ids : list name) : tactic expr :=
do
  -- When the target is a subsingleton,
  -- we can just use induction along `trunc.rec_on_subsingleton`,
  -- generating just a single goal.
  [(_, [e], _)] ← tactic.induction e ids `trunc.rec_on_subsingleton,
  return e

/-- Auxiliary tactic for `trunc_cases`. -/
private meta def trunc_cases_nondependent (e : expr) (ids : list name) : tactic expr :=
do
  -- We may as well just use `trunc.lift_on`.
  -- (It would be nice if we could use the `induction` tactic with non-dependent recursors, too?)
  -- (In fact, the general strategy works just as well here,
  -- except that it leaves a beta redex in the invariance goal.)
  to_expr ``(trunc.lift_on %%e) >>= tactic.fapply,
  -- Replace the hypothesis `e` with the unboxed version.
  tactic.clear e,
  e ← tactic.intro e.local_pp_name,
  -- In the invariance goal, introduce the two arguments using the specified identifiers
  tactic.swap,
  match ids.nth 1 with
  | some n := tactic.intro n
  | none := tactic.intro1
  end,
  match ids.nth 2 with
  | some n := tactic.intro n
  | none := tactic.intro1
  end,
  tactic.swap,
  return e

/-- Auxiliary tactic for `trunc_cases`. -/
private meta def trunc_cases_dependent (e : expr) (ids : list name) : tactic expr :=
do
  -- If all else fails, just use the general induction principle.
  [(_, [e], _), (_, [e_a, e_b, e_p], _)] ← tactic.induction e ids,
  -- However even now we can do something useful:
  -- the invariance goal has a useless `e_p : true` hypothesis,
  -- and after casing on that we may be able to simplify away
  -- the `eq.rec`.
  swap, (tactic.cases e_p >> `[try { simp only [eq_rec_constant] }]), swap,
  return e

namespace interactive

setup_tactic_parser

/--
`trunc_cases e` performs case analysis on a `trunc` expression `e`,
attempting the following strategies:
1. when the goal is a subsingleton, calling `induction e using trunc.rec_on_subsingleton`,
2. when the goal does not depend on `e`, calling `fapply trunc.lift_on e`,
   and using `intro` and `clear` afterwards to make the goals look like we used `induction`,
3. otherwise, falling through to `trunc.rec_on`, and in the new invariance goal
   calling `cases h_p` on the useless `h_p : true` hypothesis,
   and then attempting to simplify the `eq.rec`.

`trunc_cases e with h` names the new hypothesis `h`.
If `e` is a local hypothesis already,
`trunc_cases` defaults to reusing the same name.

`trunc_cases e with h h_a h_b` will use the names `h_a` and `h_b` for the new hypothesis
in the invariance goal if `trunc_cases` uses `trunc.lift_on` or `trunc.rec_on`.

Finally, if the new hypothesis from inside the `trunc` is a type class,
`trunc_cases` resets the instance cache so that it is immediately available.
-/
meta def trunc_cases (e : parse texpr) (ids : parse with_ident_list) : tactic unit :=
do
  e ← to_expr e,
  -- If `ids = []` and `e` is a local constant, we'll want to give
  -- the new unboxed hypothesis the same name.
  let ids := if ids = [] ∧ e.is_local_constant then [e.local_pp_name] else ids,
  -- Make a note of the expr `e`, or reuse `e` if it is already a local constant.
  e ← if e.is_local_constant then
        return e
      else
        (do n ← match ids.nth 0 with | some n := pure n | none := mk_fresh_name end, note n none e),
  -- Now check if the target is a subsingleton.
  tgt ← target,
  ss ← succeeds (mk_app `subsingleton [tgt] >>= mk_instance),
  -- In each branch here, we're going to capture the name of the new unboxed hypothesis
  -- so that we can later check if it's a typeclass and if so unfreeze local instances.
  e ← if ss then trunc_cases_subsingleton e ids
      else if e.occurs tgt then trunc_cases_dependent e ids
      else trunc_cases_nondependent e ids,
  c ← infer_type e >>= is_class,
  when c reset_instance_cache

end interactive
end tactic

add_tactic_doc
{ name                     := "trunc_cases",
  category                 := doc_category.tactic,
  decl_names               := [`tactic.interactive.trunc_cases],
  tags                     := ["case bashing"] }
