/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.equiv.functor

/-!
# The `equiv_rw` tactic, which transports goals or hypotheses along equivalences.
-/

namespace tactic

/-- A hard-coded list of names of lemmas used for constructing congruence equivalences. -/
-- PROJECT this should not be a hard-coded list.
-- We could accommodate most of them with `equiv_functor`, or `equiv_bifunctor` instances.
-- Moreover, these instances can typically be `derive`d.
-- Even better, they would be `category_theory.functorial` instances
-- (at that point, we could write along an isomorphism of rings `R ≅ S` and
--  automatically have `mv_polynomial.ring_equiv_congr`
--  produce an isomorphism of polynomials with those coefficients.).
def equiv_congr_lemmas : list name :=
[-- these are functorial w.r.t equiv, and so could be subsumed by a `equiv_functor.map`
 `equiv.perm_congr, `equiv.equiv_congr, `equiv.unique_congr,
 -- these are bifunctors, and so could be subsumed by a `bifunctor.map_equiv`
 `equiv.sum_congr, `equiv.prod_congr,
 -- this is technically a bifunctor `Typeᵒᵖ → Type → Type`, but the pattern matcher will never see this.
 `equiv.arrow_congr,
 `functor.map_equiv]

/--
Helper function for `adapt_equiv`.
Attempts to adapt the equivalence `eq` so that the left-hand-side is `ty`.
-/
meta def adapt_equiv' (eq : expr) : Π (ty : expr), tactic (expr × bool)
| ty :=
do
  `(%%α ≃ %%β) ← infer_type eq | fail format!"{eq} must be an `equiv`",
  if ty = α then
    return (eq, tt)
  else
    if ¬ α.occurs ty then
      (λ e, (e, ff)) <$> to_expr ``(equiv.refl %%ty)
    else (do
      initial_goals ← get_goals,
      g ← to_expr ``(%%ty ≃ _) >>= mk_meta_var,
      set_goals [g],
      let apply_and_adapt (n : name) : tactic (expr × bool) := (do
        -- Apply the named lemma
        mk_const n >>= tactic.eapply,
        -- Collect the resulting goals, then restore the original context before proceeding
        gs ← get_goals,
        set_goals initial_goals,
        -- For each of the subsidiary goals, check it is of the form `_ ≃ _`,
        -- and then if we can recursively solve it using `adapt_equiv'`.
        ns ← gs.mmap (λ g, do
          `(%%p ≃ _) ← infer_type g,
          (e, n) ← adapt_equiv' p,
          unify g e,
          return n),
        -- If so, return the new equivalence constructed via `apply`.
        g ← instantiate_mvars g,
        return (g, tt ∈ ns)),
      equiv_congr_lemmas.any_of apply_and_adapt) <|>
    fail format!"could not adapt {eq} to the form `{ty} ≃ _`"

/--
`adapt_equiv t e` "adapts" the equivalence `e`, producing a new equivalence with left-hand-side `t`.
-/
meta def adapt_equiv (ty : expr) (eq : expr) : tactic expr :=
do (e, n) ← adapt_equiv' eq ty,
   guard n,
   return e

/--
Attempt to replace the hypothesis with name `x : α`
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
  j ← mk_fresh_name,
  intro j,
  k ← mk_fresh_name,
  -- Finally, we subst along `k`, hopefully removing all the occurrences of the original `x`,
  intro k >>= subst,
  -- and then rename `j` back to `x`.
  rename j x,
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
It will also try rewriting under functors, so it can also turn
a goal of `⊢ option α` into `⊢ option β`.

(Note that rewriting hypotheses does not understand functors.)
-/
-- PROJECT Rewriting hypotheses under functors.
-- PROJECT
-- Many constructions are not strictly functorial,
-- but are functorial with respect to `≃`.
-- PROJECT More generally, rewriting along categorical isomorphisms, under functors.
-- (See the `hygienic` branch of mathlib.)
meta def equiv_rw (e : parse texpr) (loc : parse $ (tk "at" *> ident)?) : itactic :=
do e ← to_expr e,
   match loc with
   | (some hyp) := tactic.equiv_rw_hyp hyp e
   | none := do t ← target,
                e ← adapt_equiv t e,
                s ← to_expr ``(equiv.inv_fun %%e),
                tactic.eapply s,
                skip
   end

add_tactic_doc
{ name        := "equiv_rw",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.equiv_rw],
  tags        := ["rewriting", "equiv", "transport"] }

end tactic.interactive
