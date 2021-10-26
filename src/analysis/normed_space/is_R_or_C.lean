/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import analysis.normed_space.operator_norm
import analysis.complex.basic

/-!
# Normed spaces over R or C

This file is about results on normed spaces over the fields `ℝ` and `ℂ`.

## Main definitions

None.

## Main theorems

* `continuous_linear_map.op_norm_bound_of_ball_bound`: A bound on the norms of values of a linear
  map in a ball yields a bound on the operator norm.

## Notes

This file exists mainly to avoid importing `is_R_or_C` in the main normed space theory files.
-/

open metric

variables {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E]

lemma linear_map.bound_of_sphere_bound
  {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] 𝕜)
  (h : ∀ z ∈ sphere (0 : E) r, ∥ f z ∥ ≤ c) (z : E) : ∥ f z ∥ ≤ c / r * ∥ z ∥ :=
begin
  by_cases z_zero : z = 0,
  { rw z_zero, simp only [linear_map.map_zero, norm_zero, mul_zero], },
  have norm_z_eq : ∥(∥ z ∥ : 𝕜)∥ =  ∥ z ∥,
  { unfold_coes,
    simp only [norm_algebra_map_eq, ring_hom.to_fun_eq_coe, norm_norm], },
  have norm_r_eq : ∥(r : 𝕜)∥ = r,
  { rw [is_R_or_C.norm_eq_abs, is_R_or_C.abs_of_real],
    exact abs_of_pos r_pos, },
  set z₁ := (r * ∥ z ∥⁻¹ : 𝕜) • z with hz₁,
  have norm_f_z₁ : ∥ f z₁ ∥ ≤ c,
  { apply h z₁,
    rw [mem_sphere_zero_iff_norm, hz₁, norm_smul, normed_field.norm_mul],
    simp only [normed_field.norm_inv],
    rw [norm_z_eq, mul_assoc, inv_mul_cancel (norm_pos_iff.mpr z_zero).ne.symm, mul_one],
    unfold_coes,
    simp only [norm_algebra_map_eq, ring_hom.to_fun_eq_coe],
    exact abs_of_pos r_pos, },
  have r_ne_zero : (r : 𝕜) ≠ 0 := (algebra_map ℝ 𝕜).map_ne_zero.mpr r_pos.ne.symm,
  have eq : f z = ∥ z ∥ / r * (f z₁),
  { rw [hz₁, linear_map.map_smul, smul_eq_mul],
    rw [← mul_assoc, ← mul_assoc, div_mul_cancel _ r_ne_zero, mul_inv_cancel, one_mul],
    simp only [z_zero, is_R_or_C.of_real_eq_zero, norm_eq_zero, ne.def, not_false_iff], },
  rw [eq, normed_field.norm_mul, normed_field.norm_div, norm_z_eq, norm_r_eq,
      div_mul_eq_mul_div, div_mul_eq_mul_div, mul_comm],
  apply div_le_div _ _ r_pos rfl.ge,
  { exact mul_nonneg ((norm_nonneg _).trans norm_f_z₁) (norm_nonneg z), },
  apply mul_le_mul norm_f_z₁ rfl.le (norm_nonneg z) ((norm_nonneg _).trans norm_f_z₁),
end

lemma linear_map.bound_of_ball_bound
  {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] 𝕜)
  (h : ∀ z ∈ closed_ball (0 : E) r, ∥ f z ∥ ≤ c) :
  ∀ (z : E), ∥ f z ∥ ≤ c / r * ∥ z ∥ :=
begin
  apply linear_map.bound_of_sphere_bound r_pos c f,
  exact λ z hz, h z hz.le,
end

lemma continuous_linear_map.op_norm_bound_of_ball_bound
  {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →L[𝕜] 𝕜)
  (h : ∀ z ∈ closed_ball (0 : E) r, ∥ f z ∥ ≤ c) : ∥ f ∥ ≤ c / r :=
begin
  apply continuous_linear_map.op_norm_le_bound,
  { apply div_nonneg _ r_pos.le,
    exact (norm_nonneg _).trans
          (h 0 (by simp only [norm_zero, mem_closed_ball, dist_zero_left, r_pos.le])), },
  apply linear_map.bound_of_ball_bound r_pos,
  exact λ z hz, h z hz,
end
