/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import analysis.calculus.fderiv.basic

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

section continuous_linear_map
/-!
### Continuous linear maps

There are currently two variants of these in mathlib, the bundled version
(named `continuous_linear_map`, and denoted `E →L[𝕜] F`), and the unbundled version (with a
predicate `is_bounded_linear_map`). We give statements for both versions. -/

protected theorem continuous_linear_map.has_strict_fderiv_at {x : E} :
  has_strict_fderiv_at e e x :=
(is_o_zero _ _).congr_left $ λ x, by simp only [e.map_sub, sub_self]

protected lemma continuous_linear_map.has_fderiv_at_filter :
  has_fderiv_at_filter e e x L :=
(is_o_zero _ _).congr_left $ λ x, by simp only [e.map_sub, sub_self]

protected lemma continuous_linear_map.has_fderiv_within_at : has_fderiv_within_at e e s x :=
e.has_fderiv_at_filter

protected lemma continuous_linear_map.has_fderiv_at : has_fderiv_at e e x :=
e.has_fderiv_at_filter

@[simp] protected lemma continuous_linear_map.differentiable_at : differentiable_at 𝕜 e x :=
e.has_fderiv_at.differentiable_at

protected lemma continuous_linear_map.differentiable_within_at : differentiable_within_at 𝕜 e s x :=
e.differentiable_at.differentiable_within_at

@[simp] protected lemma continuous_linear_map.fderiv : fderiv 𝕜 e x = e :=
e.has_fderiv_at.fderiv

protected lemma continuous_linear_map.fderiv_within (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 e s x = e :=
begin
  rw differentiable_at.fderiv_within e.differentiable_at hxs,
  exact e.fderiv
end

@[simp] protected lemma continuous_linear_map.differentiable : differentiable 𝕜 e :=
λx, e.differentiable_at

protected lemma continuous_linear_map.differentiable_on : differentiable_on 𝕜 e s :=
e.differentiable.differentiable_on

lemma is_bounded_linear_map.has_fderiv_at_filter (h : is_bounded_linear_map 𝕜 f) :
  has_fderiv_at_filter f h.to_continuous_linear_map x L :=
h.to_continuous_linear_map.has_fderiv_at_filter

lemma is_bounded_linear_map.has_fderiv_within_at (h : is_bounded_linear_map 𝕜 f) :
  has_fderiv_within_at f h.to_continuous_linear_map s x :=
h.has_fderiv_at_filter

lemma is_bounded_linear_map.has_fderiv_at (h : is_bounded_linear_map 𝕜 f) :
  has_fderiv_at f h.to_continuous_linear_map x  :=
h.has_fderiv_at_filter

lemma is_bounded_linear_map.differentiable_at (h : is_bounded_linear_map 𝕜 f) :
  differentiable_at 𝕜 f x :=
h.has_fderiv_at.differentiable_at

lemma is_bounded_linear_map.differentiable_within_at (h : is_bounded_linear_map 𝕜 f) :
  differentiable_within_at 𝕜 f s x :=
h.differentiable_at.differentiable_within_at

lemma is_bounded_linear_map.fderiv (h : is_bounded_linear_map 𝕜 f) :
  fderiv 𝕜 f x = h.to_continuous_linear_map :=
has_fderiv_at.fderiv (h.has_fderiv_at)

lemma is_bounded_linear_map.fderiv_within (h : is_bounded_linear_map 𝕜 f)
  (hxs : unique_diff_within_at 𝕜 s x) : fderiv_within 𝕜 f s x = h.to_continuous_linear_map :=
begin
  rw differentiable_at.fderiv_within h.differentiable_at hxs,
  exact h.fderiv
end

lemma is_bounded_linear_map.differentiable (h : is_bounded_linear_map 𝕜 f) :
  differentiable 𝕜 f :=
λx, h.differentiable_at

lemma is_bounded_linear_map.differentiable_on (h : is_bounded_linear_map 𝕜 f) :
  differentiable_on 𝕜 f s :=
h.differentiable.differentiable_on

end continuous_linear_map
