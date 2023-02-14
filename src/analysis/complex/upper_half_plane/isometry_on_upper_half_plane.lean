/-
Copyright (c) 2023 Wan Ruizhe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wan Ruizhe
-/
import analysis.complex.upper_half_plane.metric
import tactic.linear_combination

/-!
This file proves that every element in SL2 acts on the upper half-plane as an isometry.

-/

open_locale upper_half_plane matrix_groups

namespace complex

lemma abs_mul (z w : ℂ) :
  abs (z * w) = abs z * abs w :=
by simp only [abs_apply, norm_sq_mul, real.sqrt_mul (norm_sq_nonneg z)]

protected lemma dist_inv_inv (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
  dist z⁻¹ w⁻¹ = (dist z w) / (abs z * abs w) :=
begin
  have h : (abs z) * (abs w) ≠ 0, { simp [hz, hw], },
  rw [eq_div_iff h, dist_eq, dist_comm, dist_eq, ← abs_mul, ← abs_mul, sub_mul,
    inv_mul_cancel_left₀ hz, mul_comm z, inv_mul_cancel_left₀ hw],
end

end complex

namespace matrix.special_linear_group

lemma fin_two_exists_eq_mk (g : SL(2, ℝ)) :
  ∃ (a b c d : ℝ) (h : a * d - b * c = 1),
    g = (⟨!![a, b; c, d], by rwa [matrix.det_fin_two_of]⟩ : SL(2, ℝ)) :=
begin
  obtain ⟨m, h⟩ := g,
  refine ⟨m 0 0, m 0 1, m 1 0, m 1 1, _, _⟩,
  { rwa m.det_fin_two at h, },
  { ext i j, fin_cases i; fin_cases j; refl, },
end

lemma fin_two_exists_eq_mk_of_apply_zero_one_eq_zero (g : SL(2, ℝ)) (hg : g 1 0 = 0) :
  ∃ (a b : ℝ) (h : a ≠ 0),
    g = (⟨!![a, b; 0, a⁻¹], by simp [h]⟩ : SL(2, ℝ)) :=
begin
  obtain ⟨m, h⟩ := g,
  replace hg : m 1 0 = 0 := by simpa using hg,
  rw [matrix.det_fin_two, hg, mul_zero, sub_zero] at h,
  have hd : m 1 1 = (m 0 0)⁻¹, { exact eq_inv_of_mul_eq_one_right h, },
  refine ⟨m 0 0, m 0 1, λ hc, _, _⟩,
  { rw [hc, zero_mul] at h,
    exact zero_ne_one h, },
  { ext i j, fin_cases i; fin_cases j; [trivial, trivial, assumption, assumption], },
end

end matrix.special_linear_group

namespace upper_half_plane

@[simp] lemma mk_im' (z : ℂ) (h) : im (⟨z, h⟩ : ℍ) = z.im := rfl

lemma im_inv_neg_coe_pos (z : ℍ) : 0 < ((-z : ℂ)⁻¹).im :=
by simpa using div_pos z.property (norm_sq_pos z)

lemma special_linear_group_apply (g : SL(2, ℝ)) (z : ℍ) :
  g • z = mk ((((g 0 0) : ℂ) * z + ((g 0 1) : ℂ)) /
              (((g 1 0) : ℂ) * z + ((g 1 1) : ℂ))) (g • z).property :=
rfl

/-- An element of `SL(2, ℝ)` representing the Mobiüs transformation `z ↦ -1/z`.

This defines an involutive elliptic isometry of the hyperbolic plane, fixing `i` and rotating
(hyperbolically) by `π`. -/
def involute : SL(2, ℝ) := ⟨!![0, -1; 1, 0], by norm_num [matrix.det_fin_two_of]⟩

@[simp] lemma involute_apply (z : ℍ) : involute • z = mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos :=
begin
  rw [special_linear_group_apply],
  simp [involute, neg_div, inv_neg],
end

lemma im_involute_smul (z : ℍ) : (involute • z).im = z.im / (z : ℂ).norm_sq := by simp

lemma exists_SL2_smul_eq_of_apply_zero_one_eq_zero (g : SL(2, ℝ)) (hc : g 1 0 = 0) :
  ∃ (u : {x : ℝ // 0 < x}) (v : ℝ),
    ((•) g : ℍ → ℍ) = (λ z, v +ᵥ z) ∘ (λ z, u • z) :=
begin
  obtain ⟨a, b, ha, rfl⟩ := g.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero hc,
  refine ⟨⟨_, mul_self_pos.mpr ha⟩, b * a, _⟩,
  ext1 ⟨z, hz⟩, ext1,
  suffices : ↑a * z * a + b * a = b * a + a * a * z,
  { rw special_linear_group_apply, simpa [add_mul], },
  ring,
end

lemma exists_SL2_smul_eq_of_apply_zero_one_ne_zero (g : SL(2, ℝ)) (hc : g 1 0 ≠ 0) :
  ∃ (u : {x : ℝ // 0 < x}) (v w : ℝ),
    ((•) g : ℍ → ℍ) = (λ z, w +ᵥ z) ∘ (λ z, involute • z) ∘ (λ z, v +ᵥ z) ∘ (λ z, u • z) :=
begin
  have h_denom := denom_ne_zero g,
  obtain ⟨a, b, c, d, h, rfl⟩ := g.fin_two_exists_eq_mk,
  replace hc : c ≠ 0, { simpa using hc, },
  refine ⟨⟨_, mul_self_pos.mpr hc⟩, c * d, a / c, _⟩,
  ext1 ⟨z, hz⟩, ext1,
  suffices : (↑a * z + b) / (↑c * z + d) = a / c - (c * d + ↑c * ↑c * z)⁻¹,
  { rw special_linear_group_apply, simpa [-neg_add_rev, inv_neg, ← sub_eq_add_neg], },
  replace hc : (c : ℂ) ≠ 0, { norm_cast, assumption, },
  replace h_denom : ↑c * z + d ≠ 0, { simpa using h_denom ⟨z, hz⟩, },
  have h_aux : (c : ℂ) * d + ↑c * ↑c * z ≠ 0,
  { rw [mul_assoc, ← mul_add, add_comm], exact mul_ne_zero hc h_denom, },
  replace h : (a * d - b * c : ℂ) = (1 : ℂ), { norm_cast, assumption, },
  field_simp,
  linear_combination (-(z * ↑c ^ 2) - ↑c * ↑d) * h, -- Courtesy of `polyrith`
end

lemma isometry_involute : isometry (λ z, involute • z : ℍ → ℍ) :=
begin
  refine isometry.of_dist_eq (λ y₁ y₂, _),
  have h₁ : 0 ≤ im y₁ * im y₂ := mul_nonneg y₁.property.le y₂.property.le,
  have h₂ : complex.abs (y₁ * y₂) ≠ 0, { simp [y₁.ne_zero, y₂.ne_zero], },
  simp only [dist_eq, involute_apply, inv_neg, neg_div, div_mul_div_comm, coe_mk, mk_im,
    complex.inv_im, complex.neg_im, coe_im, neg_neg, complex.norm_sq_neg, mul_eq_mul_left_iff,
    real.arsinh_inj, bit0_eq_zero, one_ne_zero, or_false, dist_neg_neg, mul_neg, neg_mul,
    complex.dist_inv_inv _ _ y₁.ne_zero y₂.ne_zero, ← complex.abs_mul, ← complex.norm_sq_mul,
    real.sqrt_div h₁, ← complex.abs_apply, mul_div (2 : ℝ), div_div_div_comm, div_self h₂, div_one],
end

lemma isometry_SL2_smul (g : SL(2, ℝ)) : isometry ((•) g : ℍ → ℍ) :=
begin
  by_cases hc : g 1 0 = 0,
  { obtain ⟨u, v, h⟩ := exists_SL2_smul_eq_of_apply_zero_one_eq_zero g hc,
    rw h,
    exact (isometry_real_vadd v).comp (isometry_pos_mul u), },
  { obtain ⟨u, v, w, h⟩ := exists_SL2_smul_eq_of_apply_zero_one_ne_zero g hc,
    rw h,
    exact (isometry_real_vadd w).comp (isometry_involute.comp $ (isometry_real_vadd v).comp $
      isometry_pos_mul u), },
end

end upper_half_plane
