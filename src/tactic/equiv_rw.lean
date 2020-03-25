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

-- Because Lean can't unify `?l_1` with `imax (1 ?m_1)`, I was running into trouble with the
-- version of equiv.arrow_congr that worked with `Sort*`.
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
 -- these are bifunctors, and so could be subsumed by a `bifunctor.map_equiv`
 `equiv.sum_congr, `equiv.prod_congr,
 -- this is technically a bifunctor `Typeᵒᵖ → Type → Type`, but the pattern matcher will never see this.
 `equiv.arrow_congr',
 `equiv.sigma_congr_left', -- allows rewriting in the argument of a sigma-type
 `equiv.Pi_congr_left', -- allows rewriting in the argument of a pi-type
--  `equiv.Pi_congr', -- allows rewriting in the value of a pi-type??
 `functor.map_equiv,  -- handles `list`, `option`, and many others
 `equiv.refl]

declare_trace adapt_equiv

-- meta def hack_apply (e : expr) : tactic (list (name × expr)) :=
-- do
--   g :: gs ← get_goals,
--   `(%%ty ≃ _) ← infer_type g | tactic.apply e,
--   g' ← to_expr ``(%%ty ≃ _) >>= mk_meta_var,
--   set_goals (g' :: gs),
--   r ← tactic.apply e,
--   trace "!",
--   g' ← instantiate_mvars g',
--   g ← instantiate_mvars g,
--   infer_type g' >>= (λ t, pp (g', t)) >>= trace,
--   infer_type g >>= (λ t, pp (g, t)) >>= trace,
--   unify g g',
--   return r

meta def adapt_equiv_2 (eq α ty : expr) : tactic expr :=
do
  initial_goals ← get_goals,
  g ← to_expr ``(%%ty ≃ _) >>= mk_meta_var,
  set_goals [g],
  equiv_congr_lemmas ← equiv_congr_lemmas.mmap mk_const,
  solve_by_elim {
    use_symmetry := false,
    use_exfalso := false,
    lemmas := some (eq :: equiv_congr_lemmas),
    max_steps := 10, -- TODO decide what to put here
    accept := λ goals, lock_tactic_state (do
      when_tracing `adapt_equiv (do
        goals.mmap pp >>= λ goals, trace format!"So far, we've built: {goals}"),
      goals.any_of (eq.may_occur) <|>
        (trace_if_enabled `adapt_equiv format!"Rejected, result does not contain {eq}" >> failed),
      done <|>
      when_tracing `adapt_equiv (do
        g ← target >>= pp,
        trace format!"Attempting to adapt to {g}"))
  },
  -- r ← instantiate_mvars g,
  set_goals initial_goals,
  return g

/--
Helper function for `adapt_equiv`.
Attempts to adapt the equivalence `eq : α ≃ _` so that the left-hand-side is `ty`.
-/
meta def adapt_equiv' (eq α : expr) : Π (ty : expr), tactic (expr × bool)
| ty :=
do
  when_tracing `adapt_equiv (do
    ty_pp ← pp ty,
    trace format!"Attempting to adapt to `{ty_pp} ≃ _`."),
  if ty = α then (do
    trace_if_enabled `adapt_equiv "Solving use original equiv.",
    return (eq, tt))
  else
    -- TODO with better flow control, could we just add `equiv.refl to the list of lemmas?
    if ¬ α.occurs ty then (do
      trace_if_enabled `adapt_equiv "Solving use `equiv.refl _`.",
      (λ e, (e, ff)) <$> to_expr ``(equiv.refl %%ty))
    else
    (do
      initial_goals ← get_goals,
      g ← to_expr ``(%%ty ≃ _) >>= mk_meta_var,
      set_goals [g],
      let apply_and_adapt (n : name) : tactic (expr × bool) := (do
        -- Apply the named lemma
        mk_const n >>= tactic.fapply,
        trace_if_enabled `adapt_equiv format!"Successfully applied lemma {n}",
        all_goals (intros >> skip), -- TODO explain why?
        -- Collect the resulting goals, then restore the original context before proceeding
        gs ← get_goals,
        set_goals initial_goals,
        -- For each of the subsidiary goals, check it is of the form `_ ≃ _`,
        -- and then if we can recursively solve it using `adapt_equiv'`.
        ns ← gs.mmap (λ g, do
          -- infer_type g >>= pp >>= trace_for `adapt_equiv,
          `(%%p ≃ _) ← infer_type g | return ff,
          (e, n) ← adapt_equiv' p,
          unify g e,
          return n),
        -- If so, return the new equivalence constructed via `apply`.
        g ← instantiate_mvars g,
        return (g, tt ∈ ns)),
      equiv_congr_lemmas.any_of apply_and_adapt) <|>
    (do ty_pp ← pp ty,
        eq_pp ← pp eq,
        fail format!"Could not adapt {eq_pp} to the form `{ty_pp} ≃ _`")

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
  adapt_equiv_2 eq α ty
  -- (e, n) ← adapt_equiv' eq α ty,
  -- guard n,
  -- return e

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
  intro k >>= subst,
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
