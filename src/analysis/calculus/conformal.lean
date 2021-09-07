/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import analysis.normed_space.conformal_linear_map

/-!
# Conformal Maps

A continuous linear map between real normed spaces `X` and `Y` is `conformal_at` some point `x`
if it is real differentiable at that point and its differential `is_conformal_linear_map`.

## Main definitions

* `conformal_at`: the main definition of conformal maps
* `conformal`: maps that are conformal at every point
* `conformal_factor_at`: the conformal factor of a conformal map at some point

## Main results
* The conformality of the composition of two conformal maps, the identity map
  and multiplications by nonzero constants
* `conformal_at_iff_is_conformal_map_fderiv`: an equivalent definition of the conformality of a map
* `conformal_at_iff`: an equivalent definition of the conformality of a map
* `conformal_at.preserves_angle`: if a map is conformal at `x`, then its differential
                                  preserves all angles at `x`

## Tags

conformal

## Warning

The definition of conformality in this file does NOT require the maps to be orientation-preserving.
Maps such as the complex conjugate are considered to be conformal.
-/

noncomputable theory

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F]
  {X Y Z : Type*} [normed_group X] [normed_group Y] [normed_group Z]
  [normed_space ℝ X] [normed_space ℝ Y] [normed_space ℝ Z]

section loc_conformality

open linear_isometry continuous_linear_map
open_locale real_inner_product_space

/-- A map `f` is said to be conformal if it has a conformal differential `f'`. -/
def conformal_at (f : X → Y) (x : X) :=
∃ (f' : X →L[ℝ] Y), has_fderiv_at f f' x ∧ is_conformal_map f'

lemma conformal_at_id (x : X) : conformal_at id x :=
⟨id ℝ X, has_fderiv_at_id _, is_conformal_map_id⟩

lemma conformal_at_const_smul {c : ℝ} (h : c ≠ 0) (x : X) :
  conformal_at (λ (x': X), c • x') x :=
⟨c • continuous_linear_map.id ℝ X,
  (has_fderiv_at_id x).const_smul c, is_conformal_map_const_smul h⟩

/-- A function is a conformal map if and only if its differential is a conformal linear map-/
lemma conformal_at_iff_is_conformal_map_fderiv {f : X → Y} {x : X} :
  conformal_at f x ↔ is_conformal_map (fderiv ℝ f x) :=
begin
  split,
  { rintros ⟨c, hf, hf'⟩,
    rw hf.fderiv,
    exact hf' },
  { intros H,
    by_cases h : differentiable_at ℝ f x,
    { exact ⟨fderiv ℝ f x, h.has_fderiv_at, H⟩, },
    { cases subsingleton_or_nontrivial X with w w; resetI,
      { exact ⟨(0 : X →L[ℝ] Y), has_fderiv_at_of_subsingleton f x,
        is_conformal_map_of_subsingleton 0⟩, },
      { exfalso,
        exact H.ne_zero (fderiv_zero_of_not_differentiable_at h), }, }, },
end

/-- A real differentiable map `f` is conformal at point `x` if and only if its
    differential `fderiv ℝ f x` at that point scales every inner product by a positive scalar. -/
lemma conformal_at_iff' {f : E → F} {x : E} :
  conformal_at f x ↔
  ∃ (c : ℝ), 0 < c ∧ ∀ (u v : E), ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = c * ⟪u, v⟫ :=
by rw [conformal_at_iff_is_conformal_map_fderiv, is_conformal_map_iff]

/-- A real differentiable map `f` is conformal at point `x` if and only if its
    differential `f'` at that point scales every inner product by a positive scalar. -/
lemma conformal_at_iff {f : E → F} {x : E} {f' : E →L[ℝ] F} (h : has_fderiv_at f f' x) :
  conformal_at f x ↔ ∃ (c : ℝ), 0 < c ∧ ∀ (u v : E), ⟪f' u, f' v⟫ = c * ⟪u, v⟫ :=
by simp only [conformal_at_iff', h.fderiv]

namespace conformal_at

lemma differentiable_at {f : X → Y} {x : X} (h : conformal_at f x) :
  differentiable_at ℝ f x :=
let ⟨_, h₁, _⟩ := h in h₁.differentiable_at

lemma congr {f g : X → Y} {x : X} {u : set X} (hx : x ∈ u) (hu : is_open u)
  (hf : conformal_at f x) (h : ∀ (x : X), x ∈ u → g x = f x) :
  conformal_at g x :=
let ⟨f', hfderiv, hf'⟩ := hf in
  ⟨f', hfderiv.congr_of_eventually_eq ((hu.eventually_mem hx).mono h), hf'⟩

lemma comp {f : X → Y} {g : Y → Z} (x : X)
  (hg : conformal_at g (f x)) (hf : conformal_at f x) : conformal_at (g ∘ f) x :=
begin
  rcases hf with ⟨f', hf₁, cf⟩,
  rcases hg with ⟨g', hg₁, cg⟩,
  exact ⟨g'.comp f', hg₁.comp x hf₁, cg.comp cf⟩,
end

lemma const_smul {f : X → Y} {x : X} {c : ℝ} (hc : c ≠ 0) (hf : conformal_at f x) :
  conformal_at (c • f) x :=
(conformal_at_const_smul hc $ f x).comp x hf

/-- The conformal factor of a conformal map at some point `x`. Some authors refer to this function
    as the characteristic function of the conformal map. -/
def conformal_factor_at {f : E → F} {x : E} (h : conformal_at f x) : ℝ :=
classical.some (conformal_at_iff'.mp h)

lemma conformal_factor_at_pos {f : E → F} {x : E} (h : conformal_at f x) :
  0 < conformal_factor_at h :=
(classical.some_spec $ conformal_at_iff'.mp h).1

lemma conformal_factor_at_inner_eq_mul_inner' {f : E → F} {x : E}
  (h : conformal_at f x) (u v : E) :
  ⟪(fderiv ℝ f x) u, (fderiv ℝ f x) v⟫ = (conformal_factor_at h : ℝ) * ⟪u, v⟫ :=
(classical.some_spec $ conformal_at_iff'.mp h).2 u v

lemma conformal_factor_at_inner_eq_mul_inner {f : E → F} {x : E} {f' : E →L[ℝ] F}
  (h : has_fderiv_at f f' x) (H : conformal_at f x) (u v : E) :
  ⟪f' u, f' v⟫ = (conformal_factor_at H : ℝ) * ⟪u, v⟫ :=
(H.differentiable_at.has_fderiv_at.unique h) ▸ conformal_factor_at_inner_eq_mul_inner' H u v

end conformal_at

end loc_conformality

section global_conformality

/-- A map `f` is conformal if it's conformal at every point. -/
def conformal (f : X → Y) :=
∀ (x : X), conformal_at f x

lemma conformal_id : conformal (id : X → X) := λ x, conformal_at_id x

lemma conformal_const_smul {c : ℝ} (h : c ≠ 0) : conformal (λ (x : X), c • x) :=
λ x, conformal_at_const_smul h x

namespace conformal

lemma conformal_at {f : X → Y} (h : conformal f) (x : X) : conformal_at f x := h x

lemma differentiable {f : X → Y} (h : conformal f) : differentiable ℝ f :=
λ x, (h x).differentiable_at

lemma comp {f : X → Y} {g : Y → Z} (hf : conformal f) (hg : conformal g) : conformal (g ∘ f) :=
λ x, (hg $ f x).comp x (hf x)

lemma const_smul {f : X → Y} (hf : conformal f) {c : ℝ} (hc : c ≠ 0) : conformal (c • f) :=
λ x, (hf x).const_smul hc

end conformal

end global_conformality
