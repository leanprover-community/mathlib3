/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import analysis.normed_space.inner_product

/-!
# Conformal Linear Maps

A continuous linear map between `R`-normed spaces `X` and `Y` `is_conformal_map` if it is
a nonzero multiple of a linear isometry.

## Main definitions

* `is_conformal_map`: the main definition of conformal linear maps

## Main results

* The conformality of the composition of two conformal linear maps, the identity map
  and multiplications by nonzero constants as continuous linear maps
* `is_conformal_map_iff`: an equivalent definition of the conformality
* `is_conformal_map_of_subsingleton`: all continuous linear maps on singleton spaces are conformal
* `is_conformal_map.preserves_angle`: if a continuous linear map is conformal, then it
                                      preserves all angles in the normed space

## Tags

conformal

## Warning

The definition of conformality in this file does NOT require the maps to be orientation-preserving.
-/

noncomputable theory

open linear_isometry continuous_linear_map
open_locale real_inner_product_space

/-- A continuous linear map `f'` is said to be conformal if it's
    a nonzero multiple of a linear isometry. -/
def is_conformal_map {R : Type*} {X Y : Type*} [nondiscrete_normed_field R]
  [normed_group X] [normed_group Y] [normed_space R X] [normed_space R Y]
  (f' : X →L[R] Y) :=
∃ (c : R) (hc : c ≠ 0) (li : X →ₗᵢ[R] Y), (f' : X → Y) = c • li

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F]
  {X Y Z : Type*} [normed_group X] [normed_group Y] [normed_group Z]
  [normed_space ℝ X] [normed_space ℝ Y] [normed_space ℝ Z]
  {R M N G : Type*} [nondiscrete_normed_field R]
  [normed_group M] [normed_group N] [normed_group G]
  [normed_space R M] [normed_space R N] [normed_space R G]

lemma is_conformal_map_id : is_conformal_map (id R M) :=
⟨1, one_ne_zero, id, by ext; simp⟩

lemma is_conformal_map_const_smul {c : R} (hc : c ≠ 0) : is_conformal_map (c • (id R M)) :=
⟨c, hc, id, by ext; simp⟩

lemma linear_isometry.is_conformal_map (f' : E →ₗᵢ[ℝ] F) :
  is_conformal_map f'.to_continuous_linear_map :=
⟨1, one_ne_zero, f', by ext; simp⟩

lemma is_conformal_map_iff (f' : E →L[ℝ] F) :
  is_conformal_map f' ↔ ∃ (c : ℝ), 0 < c ∧
  ∀ (u v : E), ⟪f' u, f' v⟫ = (c : ℝ) * ⟪u, v⟫ :=
begin
  split,
  { rintros ⟨c₁, hc₁, li, h⟩,
    refine ⟨c₁ * c₁, mul_self_pos hc₁, λ u v, _⟩,
    simp only [h, pi.smul_apply, inner_map_map,
               real_inner_smul_left, real_inner_smul_right, mul_assoc], },
  { rintros ⟨c₁, hc₁, huv⟩,
    let c := real.sqrt c₁⁻¹,
    have hc : c ≠ 0 := λ w, by {simp only [c] at w;
      exact (real.sqrt_ne_zero'.mpr $ inv_pos.mpr hc₁) w},
    let f₁ := c • f',
    have minor : (f₁ : E → F) = c • f' := rfl,
    have minor' : (f' : E → F) = c⁻¹ • f₁ := by ext;
      simp_rw [minor, pi.smul_apply]; rw [smul_smul, inv_mul_cancel hc, one_smul],
    refine ⟨c⁻¹, inv_ne_zero hc, f₁.to_linear_map.isometry_of_inner (λ u v, _), minor'⟩,
    simp_rw [to_linear_map_eq_coe, continuous_linear_map.coe_coe, minor, pi.smul_apply],
    rw [real_inner_smul_left, real_inner_smul_right,
        huv u v, ← mul_assoc, ← mul_assoc,
        real.mul_self_sqrt $ le_of_lt $ inv_pos.mpr hc₁,
        inv_mul_cancel $ ne_of_gt hc₁, one_mul], },
end

lemma is_conformal_map_of_subsingleton [h : subsingleton M] (f' : M →L[R] N) :
  is_conformal_map f' :=
begin
  rw subsingleton_iff at h,
  have minor : (f' : M → N) = function.const M 0 := by ext x'; rw h x' 0; exact f'.map_zero,
  have key : ∀ (x' : M), ∥(0 : M →ₗ[R] N) x'∥ = ∥x'∥ := λ x',
    by rw [linear_map.zero_apply, h x' 0]; repeat { rw norm_zero },
  exact ⟨(1 : R), one_ne_zero, ⟨0, key⟩,
    by rw pi.smul_def; ext p; rw [one_smul, minor]; refl⟩,
end

namespace is_conformal_map

lemma comp {f' : M →L[R] N} {g' : N →L[R] G}
  (hg' : is_conformal_map g') (hf' : is_conformal_map f') :
  is_conformal_map (g'.comp f') :=
begin
  rcases hf' with ⟨cf, hcf, lif, hlif⟩,
  rcases hg' with ⟨cg, hcg, lig, hlig⟩,
  refine ⟨cg * cf, mul_ne_zero hcg hcf, lig.comp lif, funext (λ x, _)⟩,
  simp only [coe_comp', linear_isometry.coe_comp, hlif, hlig, pi.smul_apply,
             function.comp_app, linear_isometry.map_smul, smul_smul],
end

lemma injective {f' : M →L[R] N} (h : is_conformal_map f') : function.injective f' :=
let ⟨c, hc, li, hf'⟩ := h in by simp only [hf', pi.smul_def];
  exact (smul_right_injective _ hc).comp li.injective

lemma ne_zero [nontrivial M] {f' : M →L[R] N} (hf' : is_conformal_map f') :
  f' ≠ 0 :=
begin
  intros w,
  rcases exists_ne (0 : M) with ⟨a, ha⟩,
  have : f' a = f' 0,
  { simp_rw [w, continuous_linear_map.zero_apply], },
  exact ha (hf'.injective this),
end

end is_conformal_map
