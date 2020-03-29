/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.equiv.functor

/-!
# The `equiv_rw` tactic transports goals or hypotheses along equivalences.

The basic syntax is `equiv_rw e`, where `e : α ≃ β` is an equivalence.
This will try to replace occurrences of `α` in the goal with `β`, for example
transforming
* `⊢ α` with `⊢ β`,
* `⊢ option α` with `⊢ option β`
* `⊢ {a // P}` with `{b // P (⇑(equiv.symm e) b)}`

The tactic can also be used to rewrite hypotheses, using the syntax `equiv_rw e at h`.

## Implementation details

The main internal function is `equiv_rw_type e t`,
which attempts to turn an expression `e : α ≃ β` into a new equivalence with left hand side `t`.
As an example, with `t = option α`, it will generate `functor.map_equiv option e`.

This is achieved by generating a new synthetic goal `%%t ≃ _`,
and calling `solve_by_elim` with an appropriate set of congruence lemmas.
To avoid having to specify the relevant congruence lemmas by hand,
we mostly rely on `functor.map_equiv` and `bifunctor.map_equiv`
(and, in a future PR, `equiv_functor.map_equiv`, see below),
along with some structural congruence lemmas such as
* `equiv.arrow_congr'`,
* `equiv.subtype_equiv_of_subtype'`,
* `equiv.sigma_congr_left'`, and
* `equiv.Pi_congr_left'`.

The main `equiv_rw` function, when operating on the goal, simply generates a new equivalence `e'`
with left hand side matching the target, and calls `apply e'.inv_fun`.

When operating on a hypothesis `x : α`, we introduce a new fact `h : x = e.symm (e x)`,
revert this, and then attempt to `generalize`, replacing all occurrences of `e x` with a new constant `y`,
before `intro`ing and `subst`ing `h`, and renaming `y` back to `x`.

## Future improvements
While `equiv_rw` will rewrite under type-level functors (e.g. `option` and `list`),
many constructions are only functorial with respect to equivalences
(essentially, because of both positive and negative occurrences of the type being rewritten).
At the moment, we only handle constructions of this form (e.g. `unique` or `ring`) by
including explicit `equiv.*_congr` lemmas in the list provided to `solve_by_elim`.

A (near) future PR will introduce `equiv_functor`,
a typeclass for functions which are functorial with respect to equivalences,
and use these instances rather than hard-coding the `congr` lemmas here.

`equiv_functor` is not included in the initial implementation of `equiv_rw`, simply because
the best way to construct an instance of `equiv_functor has_add` is to use `equiv_rw`!
In fact, in a slightly more distant future PR I anticipate that
`derive equiv_functor` should work on many examples, and
we can incrementally bootstrap the strength of `equiv_rw`.

An ambitious project might be to add `equiv_rw!`,
a tactic which, when failing to find appropriate `equiv_functor` instances,
attempts to `derive` them on the spot.

For now `equiv_rw` is entirely based on `equiv` in `Type`,
but the framework can readily be generalised to also work with other types of equivalences,
for example specific notations such as ring equivalence (`≃+*`),
or general categorical isomorphisms (`≅`).

This will allow us to transport across more general types of equivalences,
but this will wait for another subsequent PR.
-/

namespace tactic

/-- A hard-coded list of names of lemmas used for constructing congruence equivalences. -/

-- TODO: This should not be a hard-coded list.
-- We could accommodate the remaining "non-structural" lemmas using
-- `equiv_functor` instances.
-- Moreover, these instances can typically be `derive`d.

-- (Scott): I have not incorporated `equiv_functor` as part of this PR,
-- as the best way to construct instances, either by hand or using `derive`, is to use this tactic!

-- TODO: We should also use `category_theory.functorial` and `category_theory.hygienic` instances.
-- (example goal: we could rewrite along an isomorphism of rings (either as `R ≅ S` or `R ≃+* S`)
-- and turn an `x : mv_polynomial σ R` into an `x : mv_polynomial σ S`.).

meta def equiv_congr_lemmas : tactic (list expr) :=
do exprs ←
  [
  `equiv.of_iff,
  `category_theory.iso.to_equiv,
  -- These are functorial w.r.t equiv,
  -- and so will be subsumed by `equiv_functor.map_equiv` in a subsequent PR.
  -- Many more could be added, but will wait for that framework.
  `equiv.perm_congr, `equiv.equiv_congr, `equiv.unique_congr,
  -- The function arrow is technically a bifunctor `Typeᵒᵖ → Type → Type`,
  -- but the pattern matcher will never see this.
  `equiv.arrow_congr',
  -- Allow rewriting in subtypes:
  `equiv.subtype_equiv_of_subtype',
  -- Allow rewriting in the first component of a sigma-type:
  `equiv.sigma_congr_left',
  -- Allow rewriting ∀s:
  -- (You might think that repeated application of `equiv.forall_congr'
  -- would handle the higher arity cases, but unfortunately unification is not clever enough.)
  `equiv.forall₃_congr',
  `equiv.forall₂_congr',
  `equiv.forall_congr',
  -- Allow rewriting in argument of Pi types:
   `equiv.Pi_congr_left',
  -- Handles `sum` and `prod`, and many others:
  `bifunctor.map_equiv,
  -- Handles `list`, `option`, and many others:
  `functor.map_equiv,
  `category_theory.map_iso,
  -- We have to filter results to ensure we don't cheat and use exclusively `equiv.refl` and `iff.refl`!
  `equiv.refl,
  `iff.refl
  ].mmap (λ n, try_core (mk_const n)),
  return (exprs.map option.to_list).join -- TODO: implement `.mfilter_map mk_const`?

declare_trace equiv_rw_type

/--
Configuration structure for `equiv_rw`.

* `max_steps` bounds the search depth for equivalences to rewrite along.
  The default value is 10.
  (e.g., if you're rewriting along `e : α ≃ β`, and `max_steps := 2`,
  you can rewrite `option (option α))` but not `option (option (option α))`.
-/
meta structure equiv_rw_cfg :=
(max_steps : ℕ := 10)

/--
Implementation of `equiv_rw_type`, using `solve_by_elim`.
Expects a goal of the form `t ≃ _`,
and tries to solve it using `eq : α ≃ β` and congruence lemmas.
-/
meta def equiv_rw_type_core (eq : expr) (cfg : equiv_rw_cfg) : tactic unit :=
do
  -- Assemble the relevant lemmas.
  equiv_congr_lemmas ← equiv_congr_lemmas,
  /-
    We now call `solve_by_elim` to try to generate the requested equivalence.
    There are a few subtleties!
    * We make sure that `eq` is the first lemma, so it is applied whenever possible.
    * In `equiv_congr_lemmas`, we put `equiv.refl` last so it is only used when it is not possible
      to descend further.
    * To avoid the possibility that the entire resulting expression is built out of
      congruence lemmas and `equiv.refl`, we use the `accept` subtactic of `solve_by_elim`
      to reject any results which neither contain `eq` or a remaining metavariable.
    * Since some congruence lemmas generate subgoals with `∀` statements,
      we use the `pre_apply` subtactic of `solve_by_elim` to preprocess each new goal with `intros`.
  -/
  solve_by_elim {
    use_symmetry := false,
    use_exfalso := false,
    lemmas := some (eq :: equiv_congr_lemmas),
    max_steps := cfg.max_steps,
    -- Subgoals may contain function types,
    -- and we want to continue trying to construct equivalences after the binders.
    pre_apply := tactic.intros >> skip,
    discharger := `[dsimp only [] with functoriality] <|>
      trace_if_enabled `equiv_rw_type "Failed, no congruence lemma applied!" >> failed,
    -- We accept any branch of the `solve_by_elim` search tree which
    -- either still contains metavariables, or already contains at least one copy of `eq`.
    -- This is to prevent generating equivalences built entirely out of `equiv.refl`.
    accept := λ goals, lock_tactic_state (do
      when_tracing `equiv_rw_type (do
        goals.mmap pp >>= λ goals, trace format!"So far, we've built: {goals}"),
      goals.any_of (λ g, guard $ g.contains_expr_or_mvar eq) <|>
        (trace_if_enabled `equiv_rw_type format!"Rejected, result does not contain {eq}" >> failed),
      done <|>
      when_tracing `equiv_rw_type (do
        gs ← get_goals,
        gs ← gs.mmap (λ g, infer_type g >>= pp),
        trace format!"Attempting to adapt to {gs}")) }

/--
`equiv_rw_type e t` rewrites the type `t` using the equivalence `e : α ≃ β`,
returning a new equivalence `t ≃ t'`.
-/
meta def equiv_rw_type (eq : expr) (ty : expr) (cfg : equiv_rw_cfg) : tactic expr :=
do
  when_tracing `equiv_rw_type (do
    ty_pp ← pp ty,
    eq_pp ← pp eq,
    eq_ty_pp ← infer_type eq >>= pp,
    trace format!"Attempting to rewrite the type `{ty_pp}` using `{eq_pp} : {eq_ty_pp}`."),
  -- `(_ ≃ _) ← infer_type eq | fail format!"{eq} must be an `equiv`",
  -- We prepare a synthetic goal of type `(%%ty ≃ _)`, for some placeholder right hand side.
  initial_goals ← get_goals,
  g ← to_expr ``(%%ty ≃ _) >>= mk_meta_var,
  set_goals [g],
  -- Now call `equiv_rw_type_core` to actually do the work, then restore the original goals.
  equiv_rw_type_core eq cfg,
  set_goals initial_goals,
  -- Finally, we simplify the resulting equivalence,
  -- to compress away some `map_equiv equiv.refl` subexpressions.
  instantiate_mvars g >>= (λ g, prod.fst <$> g.simp {fail_if_unchanged := ff})

/--
Attempt to replace the hypothesis with name `x`
by transporting it along the equivalence in `e : α ≃ β`.
-/
meta def equiv_rw_hyp (x : name) (e : expr) (cfg : equiv_rw_cfg := {}) : tactic unit :=
do
  x' ← get_local x,
  x_ty ← infer_type x',
  -- Adapt `e` to an equivalence with left-hand-sidee `x_ty`.
  e ← equiv_rw_type e x_ty cfg,
  eq ← to_expr ``(%%x' = equiv.symm %%e (equiv.to_fun %%e %%x')),
  prf ← to_expr ``((equiv.symm_apply_apply %%e %%x').symm),
  h ← assertv_fresh eq prf,
  -- Revert the new hypothesis, so it is also part of the goal.
  revert h,
  ex ← to_expr ``(equiv.to_fun %%e %%x'),
  -- Now call `generalize`,
  -- attempting to replace all occurrences of `e x`,
  -- calling it for now `j : β`, with `k : x = e.symm j`.
  generalize ex (by apply_opt_param) transparency.none,
  -- Reintroduce `x` (now of type `b`).
  intro x,
  k ← mk_fresh_name,
  -- Finally, we subst along `k`, hopefully removing all the occurrences of the original `x`,
  intro k >>= (λ k,
    subst_core k
    -- If we're rewriting a typeclass instance we may need to unfreeze local instances
    <|> unfreeze_local_instances >> subst_core k
    -- Sometimes (TODO?), particularly when rewriting along isomorphisms,
    -- `subst` just doesn't work, so we clean up as best we can.
    -- <|> infer_type k >>= pp >>= (λ kt, trace format!"`subst` failed: {kt}") >> clear k >> clear x'
    ),
  `[try { simp only [equiv.symm_symm, equiv.apply_symm_apply, equiv.symm_apply_apply] }],
  skip

/-- Rewrite the goal using an equiv `e`. -/
meta def equiv_rw_target (e : expr) (cfg : equiv_rw_cfg := {}) : tactic unit :=
do
  t ← target,
  e ← equiv_rw_type e t cfg,
  s ← to_expr ``(equiv.inv_fun %%e),
  tactic.eapply s,
  skip

end tactic

namespace tactic.interactive
open lean.parser
open interactive interactive.types
open tactic

local postfix `?`:9001 := optional

/--
`equiv_rw e at h`, where `h : α` is a hypothesis, and `e : α ≃ β`,
will attempt to transport `h` along `e`, producing a new hypothesis `h : β`,
with all occurrences of `h` in other hypotheses and the goal replaced with `e.symm h`.

`equiv_rw e` will attempt to transport the goal along an equivalence `e : α ≃ β`.
In its minimal form it replaces the goal `⊢ α` with `⊢ β` by calling `apply e.inv_fun`.

`equiv_rw` will also try rewriting under functors, so can turn
a hypothesis `h : list α` into `h : list β` or
a goal `⊢ option α` into `⊢ option β`.

The maximum search depth for rewriting in subexpressions is controlled by
`equiv_rw e {max_steps := n}`.
-/
meta def equiv_rw (e : parse texpr) (loc : parse $ (tk "at" *> ident)?) (cfg : equiv_rw_cfg := {}) : itactic :=
do e ← to_expr e,
   match loc with
   | (some hyp) := equiv_rw_hyp hyp e cfg
   | none := equiv_rw_target e cfg
   end

add_tactic_doc
{ name        := "equiv_rw",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.equiv_rw],
  tags        := ["rewriting", "equiv", "transport"] }

/--
Solve a goal of the form `t ≃ _`,
by constructing an equivalence from `e : α ≃ β`.
This is the same equivalence that `equiv_rw` would use to rewrite a term of type `t`.

A typical usage might be:
```
have e' : option α ≃ option β := by equiv_rw_type e
```
-/
meta def equiv_rw_type (e : parse texpr) (cfg : equiv_rw_cfg := {}) : itactic :=
do
 `(%%t ≃ _) ← target | fail "`equiv_rw_type` solves goals of the form `t ≃ _`.",
 e ← to_expr e,
 tactic.equiv_rw_type e t cfg >>= tactic.exact

add_tactic_doc
{ name        := "equiv_rw_type",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.equiv_rw_type],
  tags        := ["rewriting", "equiv", "transport"] }

end tactic.interactive
