/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import analysis.calculus.fderiv.basic

/-!
# The derivative of a composition (chain rule)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For detailed documentation of the Fréchet derivative,
see the module docstring of `analysis/calculus/fderiv/basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
composition of functions (the chain rule).
-/

open filter asymptotics continuous_linear_map set metric
open_locale topology classical nnreal filter asymptotics ennreal

noncomputable theory


section

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
variables {G' : Type*} [normed_add_comm_group G'] [normed_space 𝕜 G']

variables {f f₀ f₁ g : E → F}
variables {f' f₀' f₁' g' : E →L[𝕜] F}
variables (e : E →L[𝕜] F)
variables {x : E}
variables {s t : set E}
variables {L L₁ L₂ : filter E}


section composition
/-!
### Derivative of the composition of two functions

For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/

variable (x)

theorem has_fderiv_at_filter.comp {g : F → G} {g' : F →L[𝕜] G} {L' : filter F}
  (hg : has_fderiv_at_filter g g' (f x) L')
  (hf : has_fderiv_at_filter f f' x L) (hL : tendsto f L L') :
  has_fderiv_at_filter (g ∘ f) (g'.comp f') x L :=
let eq₁ := (g'.is_O_comp _ _).trans_is_o hf in
let eq₂ := (hg.comp_tendsto hL).trans_is_O hf.is_O_sub in
by { refine eq₂.triangle (eq₁.congr_left (λ x', _)), simp }

/- A readable version of the previous theorem,
   a general form of the chain rule. -/

example {g : F → G} {g' : F →L[𝕜] G}
  (hg : has_fderiv_at_filter g g' (f x) (L.map f))
  (hf : has_fderiv_at_filter f f' x L) :
  has_fderiv_at_filter (g ∘ f) (g'.comp f') x L :=
begin
  unfold has_fderiv_at_filter at hg,
  have := calc (λ x', g (f x') - g (f x) - g' (f x' - f x)) =o[L] (λ x', f x' - f x) :
    hg.comp_tendsto le_rfl
  ... =O[L] (λ x', x' - x) : hf.is_O_sub,
  refine this.triangle _,
  calc (λ x' : E, g' (f x' - f x) - g'.comp f' (x' - x))
      =ᶠ[L] λ x', g' (f x' - f x - f' (x' - x)) : eventually_of_forall (λ x', by simp)
  ... =O[L] λ x', f x' - f x - f' (x' - x)      : g'.is_O_comp _ _
  ... =o[L] λ x', x' - x                        : hf
end

theorem has_fderiv_within_at.comp {g : F → G} {g' : F →L[𝕜] G} {t : set F}
  (hg : has_fderiv_within_at g g' t (f x)) (hf : has_fderiv_within_at f f' s x)
  (hst : maps_to f s t) :
  has_fderiv_within_at (g ∘ f) (g'.comp f') s x :=
hg.comp x hf $ hf.continuous_within_at.tendsto_nhds_within hst

theorem has_fderiv_at.comp_has_fderiv_within_at {g : F → G} {g' : F →L[𝕜] G}
  (hg : has_fderiv_at g g' (f x)) (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (g ∘ f) (g'.comp f') s x :=
hg.comp x hf hf.continuous_within_at

theorem has_fderiv_within_at.comp_of_mem {g : F → G} {g' : F →L[𝕜] G} {t : set F}
  (hg : has_fderiv_within_at g g' t (f x)) (hf : has_fderiv_within_at f f' s x)
  (hst : tendsto f (𝓝[s] x) (𝓝[t] f x)) :
  has_fderiv_within_at (g ∘ f) (g'.comp f') s x :=
has_fderiv_at_filter.comp x hg hf hst

/-- The chain rule. -/
theorem has_fderiv_at.comp {g : F → G} {g' : F →L[𝕜] G}
  (hg : has_fderiv_at g g' (f x)) (hf : has_fderiv_at f f' x) :
  has_fderiv_at (g ∘ f) (g'.comp f') x :=
hg.comp x hf hf.continuous_at

lemma differentiable_within_at.comp {g : F → G} {t : set F}
  (hg : differentiable_within_at 𝕜 g t (f x)) (hf : differentiable_within_at 𝕜 f s x)
  (h : maps_to f s t) : differentiable_within_at 𝕜 (g ∘ f) s x :=
(hg.has_fderiv_within_at.comp x hf.has_fderiv_within_at h).differentiable_within_at

lemma differentiable_within_at.comp' {g : F → G} {t : set F}
  (hg : differentiable_within_at 𝕜 g t (f x)) (hf : differentiable_within_at 𝕜 f s x) :
  differentiable_within_at 𝕜 (g ∘ f) (s ∩ f⁻¹' t) x :=
hg.comp x (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

lemma differentiable_at.comp {g : F → G}
  (hg : differentiable_at 𝕜 g (f x)) (hf : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜 (g ∘ f) x :=
(hg.has_fderiv_at.comp x hf.has_fderiv_at).differentiable_at

lemma differentiable_at.comp_differentiable_within_at {g : F → G}
  (hg : differentiable_at 𝕜 g (f x)) (hf : differentiable_within_at 𝕜 f s x) :
  differentiable_within_at 𝕜 (g ∘ f) s x :=
hg.differentiable_within_at.comp x hf (maps_to_univ _ _)

lemma fderiv_within.comp {g : F → G} {t : set F}
  (hg : differentiable_within_at 𝕜 g t (f x)) (hf : differentiable_within_at 𝕜 f s x)
  (h : maps_to f s t) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (g ∘ f) s x = (fderiv_within 𝕜 g t (f x)).comp (fderiv_within 𝕜 f s x) :=
(hg.has_fderiv_within_at.comp x (hf.has_fderiv_within_at) h).fderiv_within hxs

/-- A version of `fderiv_within.comp` that is useful to rewrite the composition of two derivatives
  into a single derivative. This version always applies, but creates a new side-goal `f x = y`. -/
lemma fderiv_within_fderiv_within {g : F → G} {f : E → F} {x : E} {y : F} {s : set E} {t : set F}
  (hg : differentiable_within_at 𝕜 g t y) (hf : differentiable_within_at 𝕜 f s x)
  (h : maps_to f s t) (hxs : unique_diff_within_at 𝕜 s x) (hy : f x = y) (v : E) :
  fderiv_within 𝕜 g t y (fderiv_within 𝕜 f s x v) = fderiv_within 𝕜 (g ∘ f) s x v :=
by { subst y, rw [fderiv_within.comp x hg hf h hxs], refl }

/-- Ternary version of `fderiv_within.comp`, with equality assumptions of basepoints added, in
  order to apply more easily as a rewrite from right-to-left. -/
lemma fderiv_within.comp₃ {g' : G → G'} {g : F → G} {t : set F} {u : set G} {y : F} {y' : G}
  (hg' : differentiable_within_at 𝕜 g' u y') (hg : differentiable_within_at 𝕜 g t y)
  (hf : differentiable_within_at 𝕜 f s x)
  (h2g : maps_to g t u) (h2f : maps_to f s t)
  (h3g : g y = y') (h3f : f x = y) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (g' ∘ g ∘ f) s x = (fderiv_within 𝕜 g' u y').comp
    ((fderiv_within 𝕜 g t y).comp (fderiv_within 𝕜 f s x)) :=
begin
  substs h3g h3f,
  exact (hg'.has_fderiv_within_at.comp x
    (hg.has_fderiv_within_at.comp x (hf.has_fderiv_within_at) h2f) $ h2g.comp h2f).fderiv_within hxs
end

lemma fderiv.comp {g : F → G}
  (hg : differentiable_at 𝕜 g (f x)) (hf : differentiable_at 𝕜 f x) :
  fderiv 𝕜 (g ∘ f) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) :=
(hg.has_fderiv_at.comp x hf.has_fderiv_at).fderiv

lemma fderiv.comp_fderiv_within {g : F → G}
  (hg : differentiable_at 𝕜 g (f x)) (hf : differentiable_within_at 𝕜 f s x)
  (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (g ∘ f) s x = (fderiv 𝕜 g (f x)).comp (fderiv_within 𝕜 f s x) :=
(hg.has_fderiv_at.comp_has_fderiv_within_at x hf.has_fderiv_within_at).fderiv_within hxs

lemma differentiable_on.comp {g : F → G} {t : set F}
  (hg : differentiable_on 𝕜 g t) (hf : differentiable_on 𝕜 f s) (st : maps_to f s t) :
  differentiable_on 𝕜 (g ∘ f) s :=
λx hx, differentiable_within_at.comp x (hg (f x) (st hx)) (hf x hx) st

lemma differentiable.comp {g : F → G} (hg : differentiable 𝕜 g) (hf : differentiable 𝕜 f) :
  differentiable 𝕜 (g ∘ f) :=
λx, differentiable_at.comp x (hg (f x)) (hf x)

lemma differentiable.comp_differentiable_on {g : F → G} (hg : differentiable 𝕜 g)
  (hf : differentiable_on 𝕜 f s) :
  differentiable_on 𝕜 (g ∘ f) s :=
hg.differentiable_on.comp hf (maps_to_univ _ _)

/-- The chain rule for derivatives in the sense of strict differentiability. -/
protected lemma has_strict_fderiv_at.comp {g : F → G} {g' : F →L[𝕜] G}
  (hg : has_strict_fderiv_at g g' (f x)) (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, g (f x)) (g'.comp f') x :=
((hg.comp_tendsto (hf.continuous_at.prod_map' hf.continuous_at)).trans_is_O hf.is_O_sub).triangle $
  by simpa only [g'.map_sub, f'.coe_comp'] using (g'.is_O_comp _ _).trans_is_o hf

protected lemma differentiable.iterate {f : E → E} (hf : differentiable 𝕜 f) (n : ℕ) :
  differentiable 𝕜 (f^[n]) :=
nat.rec_on n differentiable_id (λ n ihn, ihn.comp hf)

protected lemma differentiable_on.iterate {f : E → E} (hf : differentiable_on 𝕜 f s)
  (hs : maps_to f s s) (n : ℕ) :
  differentiable_on 𝕜 (f^[n]) s :=
nat.rec_on n differentiable_on_id (λ n ihn, ihn.comp hf hs)

variable {x}

protected lemma has_fderiv_at_filter.iterate {f : E → E} {f' : E →L[𝕜] E}
  (hf : has_fderiv_at_filter f f' x L) (hL : tendsto f L L) (hx : f x = x) (n : ℕ) :
  has_fderiv_at_filter (f^[n]) (f'^n) x L :=
begin
  induction n with n ihn,
  { exact has_fderiv_at_filter_id x L },
  { rw [function.iterate_succ, pow_succ'],
    rw ← hx at ihn,
    exact ihn.comp x hf hL }
end

protected lemma has_fderiv_at.iterate {f : E → E} {f' : E →L[𝕜] E}
  (hf : has_fderiv_at f f' x) (hx : f x = x) (n : ℕ) :
  has_fderiv_at (f^[n]) (f'^n) x :=
begin
  refine hf.iterate _ hx n,
  convert hf.continuous_at,
  exact hx.symm
end

protected lemma has_fderiv_within_at.iterate {f : E → E} {f' : E →L[𝕜] E}
  (hf : has_fderiv_within_at f f' s x) (hx : f x = x) (hs : maps_to f s s) (n : ℕ) :
  has_fderiv_within_at (f^[n]) (f'^n) s x :=
begin
  refine hf.iterate _ hx n,
  convert tendsto_inf.2 ⟨hf.continuous_within_at, _⟩,
  exacts [hx.symm, (tendsto_principal_principal.2 hs).mono_left inf_le_right]
end

protected lemma has_strict_fderiv_at.iterate {f : E → E} {f' : E →L[𝕜] E}
  (hf : has_strict_fderiv_at f f' x) (hx : f x = x) (n : ℕ) :
  has_strict_fderiv_at (f^[n]) (f'^n) x :=
begin
  induction n with n ihn,
  { exact has_strict_fderiv_at_id x },
  { rw [function.iterate_succ, pow_succ'],
    rw ← hx at ihn,
    exact ihn.comp x hf }
end

protected lemma differentiable_at.iterate {f : E → E} (hf : differentiable_at 𝕜 f x)
  (hx : f x = x) (n : ℕ) :
  differentiable_at 𝕜 (f^[n]) x :=
(hf.has_fderiv_at.iterate hx n).differentiable_at

protected lemma differentiable_within_at.iterate {f : E → E} (hf : differentiable_within_at 𝕜 f s x)
  (hx : f x = x) (hs : maps_to f s s) (n : ℕ) :
  differentiable_within_at 𝕜 (f^[n]) s x :=
(hf.has_fderiv_within_at.iterate hx hs n).differentiable_within_at

end composition

end
