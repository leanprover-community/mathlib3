/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.equiv.functor

/-!
# The `equiv_rw` tactic, which transports goals or hypotheses along equivalences.
-/

meta def expr.may_occur (e : expr) (t : expr) : tactic unit :=
-- We can't use `t.has_meta_var` here, as that detects universe metavariables, too.
guard $ ¬ t.list_meta_vars.empty ∨ e.occurs t

-- Because Lean can't unify `?l_1` with `imax (1 ?m_1)`,
-- I was running into trouble with the standard version of `equiv.arrow_congr`,
-- that works with `Sort*`.
@[congr]
def equiv.arrow_congr' {α₁ β₁ α₂ β₂ : Type*} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) :=
equiv.arrow_congr hα hβ

namespace tactic

/-- A hard-coded list of names of lemmas used for constructing congruence equivalences. -/

-- PROJECT this should not be a hard-coded list.
-- We could accommodate most of them with `equiv_functor`, or `equiv_bifunctor` instances.
-- Moreover, these instances can typically be `derive`d.
-- (Scott): I will add these in future PRs.

-- Even better, they would be `category_theory.functorial` instances
-- (at that point, we could rewrite along an isomorphism of rings `R ≅ S` and
--  turn an `x : mv_polynomial σ R` into an `x : mv_polynomial σ S`.).
def equiv_congr_lemmas : list name :=
[-- these are functorial w.r.t equiv, and so could be subsumed by a `equiv_functor.map`
 -- many more could be added
 `equiv.perm_congr, `equiv.equiv_congr, `equiv.unique_congr,
 -- this is technically a bifunctor `Typeᵒᵖ → Type → Type`, but the pattern matcher will never see this.
 `equiv.arrow_congr',
 `equiv.subtype_equiv_of_subtype', -- allows rewriting in subtypes
 `equiv.sigma_congr_left', -- allows rewriting in the first component of a sigma-type
 `equiv.Pi_congr_left', -- allows rewriting in the argument of a pi-type
 `bifunctor.map_equiv,  -- handles `sum` and `prod`
 `functor.map_equiv,  -- handles `list`, `option`, and many others
 `equiv.refl]

declare_trace adapt_equiv

meta def adapt_equiv_core (eq α ty : expr) : tactic expr :=
do
  initial_goals ← get_goals,
  g ← to_expr ``(%%ty ≃ _) >>= mk_meta_var,
  set_goals [g],
  equiv_congr_lemmas ← equiv_congr_lemmas.mmap mk_const,
  solve_by_elim {
    use_symmetry := false,
    use_exfalso := false,
    lemmas := some (eq :: equiv_congr_lemmas),
    -- TODO decide an appropriate upper bound on search depth.
    max_steps := 6,
    -- Subgoals may contain function types,
    -- and we want to continue trying to construct equivalences after the binders.
    pre_apply := tactic.intros >> skip,
    discharger := trace_if_enabled `adapt_equiv "Failed, no congruence lemma applied!" >> failed,
    -- We accept any branch of the `solve_by_elim` search tree which
    -- either still contains metavariables, or already contains at least one copy of `eq`.
    -- This is to prevent generating equivalences built entirely out of `equiv.refl`.
    accept := λ goals, lock_tactic_state (do
      when_tracing `adapt_equiv (do
        goals.mmap pp >>= λ goals, trace format!"So far, we've built: {goals}"),
      goals.any_of (eq.may_occur) <|>
        (trace_if_enabled `adapt_equiv format!"Rejected, result does not contain {eq}" >> failed),
      done <|>
      when_tracing `adapt_equiv (do
        gs ← get_goals,
        gs ← gs.mmap (λ g, infer_type g >>= pp),
        trace format!"Attempting to adapt to {gs}"))
  },
  set_goals initial_goals,
  return g


/--
`adapt_equiv t e` "adapts" the equivalence `e`, producing a new equivalence with left-hand-side `t`.
-/
meta def adapt_equiv (ty : expr) (eq : expr) : tactic expr :=
do
  when_tracing `adapt_equiv (do
    ty_pp ← pp ty,
    eq_pp ← pp eq,
    eq_ty_pp ← infer_type eq >>= pp,
    trace format!"Attempting to adapt `{eq_pp} : {eq_ty_pp}` to produce `{ty_pp} ≃ _`."),
  `(%%α ≃ %%β) ← infer_type eq | fail format!"{eq} must be an `equiv`",
  adapt_equiv_core eq α ty

/--
Attempt to replace the hypothesis with name `x`
by transporting it along the equivalence in `e : α ≃ β`.
-/
meta def equiv_rw_hyp : Π (x : name) (e : expr), tactic unit
| x e :=
do
  x' ← get_local x,
  x_ty ← infer_type x',
  -- Adapt `e` to an equivalence with left-hand-sidee `x_ty`
  e ← adapt_equiv x_ty e,
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
  intro k >>= (λ k, subst k <|> unfreeze_local_instances >> subst k),
  `[try { simp only [equiv.symm_symm, equiv.apply_symm_apply, equiv.symm_apply_apply] }],
  skip

/-- Rewrite the goal using an equiv `e`. -/
meta def equiv_rw_target (e : expr) : tactic unit :=
do
  t ← target,
  e ← adapt_equiv t e,
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

`equiv_rw e` tries `apply e.inv_fun`,
so with `e : α ≃ β`, it turns a goal of `⊢ α` into `⊢ β`.

`equiv_rw` will also try rewriting under functors, so can turn
a hypothesis `h : list α` into `h : list β` or
a goal `⊢ option α` into `⊢ option β`.
-/
meta def equiv_rw (e : parse texpr) (loc : parse $ (tk "at" *> ident)?) : itactic :=
do e ← to_expr e,
   match loc with
   | (some hyp) := tactic.equiv_rw_hyp hyp e
   | none := tactic.equiv_rw_target e
   end

add_tactic_doc
{ name        := "equiv_rw",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.equiv_rw],
  tags        := ["rewriting", "equiv", "transport"] }

end tactic.interactive
