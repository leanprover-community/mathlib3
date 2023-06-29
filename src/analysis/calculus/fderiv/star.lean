/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import analysis.calculus.fderiv.linear
import analysis.calculus.fderiv.comp
import analysis.calculus.fderiv.equiv
import analysis.normed_space.star.basic

/-!
# Star operations on derivatives

For detailed documentation of the Fréchet derivative,
see the module docstring of `analysis/calculus/fderiv/basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of the star
operation. Note that these only apply when the field that the derivative is respect to has a trivial
star operation; which as should be expected rules out `𝕜 = ℂ`.
-/

open_locale classical


variables {𝕜 : Type*} [nontrivially_normed_field 𝕜] [star_ring 𝕜] [has_trivial_star 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [star_add_monoid F] [normed_space 𝕜 F]
  [star_module 𝕜 F] [has_continuous_star F]

variables {f : E → F}
variables {f' : E →L[𝕜] F}
variables (e : E →L[𝕜] F)
variables {x : E}
variables {s : set E}
variables {L : filter E}

theorem has_strict_fderiv_at.star (h : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') x :=
(starL' 𝕜 : F ≃L[𝕜] F).to_continuous_linear_map.has_strict_fderiv_at.comp x h

theorem has_fderiv_at_filter.star (h : has_fderiv_at_filter f f' x L) :
  has_fderiv_at_filter (λ x, star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') x L :=
(starL' 𝕜 : F ≃L[𝕜] F).to_continuous_linear_map.has_fderiv_at_filter.comp x h filter.tendsto_map

theorem has_fderiv_within_at.star (h : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') s x :=
h.star

theorem has_fderiv_at.star (h : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') x :=
h.star

lemma differentiable_within_at.star (h : differentiable_within_at 𝕜 f s x) :
  differentiable_within_at 𝕜 (λ y, star (f y)) s x :=
h.has_fderiv_within_at.star.differentiable_within_at

@[simp] lemma differentiable_within_at_star_iff :
  differentiable_within_at 𝕜 (λ y, star (f y)) s x ↔ differentiable_within_at 𝕜 f s x :=
(starL' 𝕜 : F ≃L[𝕜] F).comp_differentiable_within_at_iff

lemma differentiable_at.star (h : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜 (λ y, star (f y)) x :=
h.has_fderiv_at.star.differentiable_at

@[simp] lemma differentiable_at_star_iff :
  differentiable_at 𝕜 (λ y, star (f y)) x ↔ differentiable_at 𝕜 f x :=
(starL' 𝕜 : F ≃L[𝕜] F).comp_differentiable_at_iff

lemma differentiable_on.star (h : differentiable_on 𝕜 f s) :
  differentiable_on 𝕜 (λ y, star (f y)) s :=
λ x hx, (h x hx).star

@[simp] lemma differentiable_on_star_iff :
  differentiable_on 𝕜 (λ y, star (f y)) s ↔ differentiable_on 𝕜 f s :=
(starL' 𝕜 : F ≃L[𝕜] F).comp_differentiable_on_iff

lemma differentiable.star (h : differentiable 𝕜 f) :
  differentiable 𝕜 (λ y, star (f y)) :=
λx, (h x).star

@[simp] lemma differentiable_star_iff : differentiable 𝕜 (λ y, star (f y)) ↔ differentiable 𝕜 f :=
(starL' 𝕜 : F ≃L[𝕜] F).comp_differentiable_iff

lemma fderiv_within_star (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λ y, star (f y)) s x =
    ((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L fderiv_within 𝕜 f s x :=
(starL' 𝕜 : F ≃L[𝕜] F).comp_fderiv_within hxs

@[simp] lemma fderiv_star :
  fderiv 𝕜 (λ y, star (f y)) x = ((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L fderiv 𝕜 f x :=
(starL' 𝕜 : F ≃L[𝕜] F).comp_fderiv
