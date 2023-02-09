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

lemma matrix.special_linear_group.fin_two_exists_eq_mk (g : SL(2, ℝ)) :
  ∃ (a b c d : ℝ) (h : a * d - b * c = 1),
    g = (⟨!![a, b; c, d], by rwa [matrix.det_fin_two_of]⟩ : SL(2, ℝ)) :=
begin
  obtain ⟨m, h⟩ := g,
  refine ⟨m 0 0, m 0 1, m 1 0, m 1 1, _, _⟩,
  { rwa m.det_fin_two at h, },
  { ext i j, fin_cases i; fin_cases j; refl, },
end

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

lemma dist_SL2_smul_smul_c_zero (g : SL(2, ℝ)) (z w : ℍ) (h1 : g 1 0 = 0) :
  dist (g • z) (g • w) = dist z w :=
begin
  obtain ⟨a, b, c, d, h, hg⟩ := g.fin_two_exists_eq_mk,
  have hg00 : g 0 0 = a := by rw [hg]; refl,
  have hg01 : g 0 1 = b := by rw [hg]; refl,
  have hg10 : g 1 0 = c := by rw [hg]; refl,
  have hg11 : g 1 1 = d := by rw [hg]; refl,
  have hg00' := hg00,
  have hg01' := hg01,
  have hg10' := hg10,
  have hg11' := hg11,
  rw matrix.special_linear_group.coe_fn_eq_coe at hg00',
  rw matrix.special_linear_group.coe_fn_eq_coe at hg01',
  rw matrix.special_linear_group.coe_fn_eq_coe at hg10',
  rw matrix.special_linear_group.coe_fn_eq_coe at hg11',
  have hg := g.property,
  rw [subtype.val_eq_coe, matrix.det_fin_two] at hg,
  have hg' : (a * d - b * c : ℂ) = (1 : ℂ), norm_cast, assumption,
  rw hg10 at h1,
  have h1' : (c : ℂ) = 0, { norm_cast, assumption, },
    have h2 : (a : ℂ) ≠ 0,
    { by_contra,
      rw [h, h1] at hg',
      norm_num at hg', },
    have hg'' := hg',
    rw h1' at hg'', norm_num at hg'',
    rw mul_eq_one_iff_inv_eq₀ h2 at hg'',
    unfold dist,
    congr' 2,
    simp only [complex.dist_eq, complex.abs, absolute_value.coe_mk, mul_hom.coe_mk,
    complex.norm_sq_apply],
    refine (mul_self_inj _ _).mp _,
    { positivity, },
    { positivity, },
    simp only [← sq, div_pow, mul_pow],
    have h3 := z.property, rw subtype.val_eq_coe at h3,
    have h3' := h3, rw coe_im at h3',
    have h4 := w.property, rw subtype.val_eq_coe at h4,
    have h4' := h4, rw coe_im at h4',
    have h5 := (g • z).property, rw subtype.val_eq_coe at h5,
    have h5' := h5, rw coe_im at h5',
    have h6 := (g • w).property, rw subtype.val_eq_coe at h6,
    have h6' := h6, rw coe_im at h6',
    rw [real.sq_sqrt _, real.sq_sqrt _, real.sq_sqrt _, real.sq_sqrt _],
    { rw div_eq_div_iff,
      { rw [← coe_im (g • z), ← coe_im (g • w), special_linear_group_apply g z,
          special_linear_group_apply g w],
        simp [hg00', hg01', hg10', hg11', h1', ← hg''],
        ring, },
      { positivity, },
      { positivity, }, },
    { positivity, },
    { positivity, },
    { positivity, },
    { positivity, },
end

lemma dist_SL2_eq_comp_c_nonzero (g : SL(2, ℝ)) (z : ℍ) (h1 : 0 < ((g 1 0 : ℝ) * (g 1 0 : ℝ))) :
  g • z = (has_vadd.vadd ((g 0 0 : ℝ) / (g 1 0 : ℝ)) ∘ has_smul.smul involute ∘ has_vadd.vadd
  ((g 1 0 : ℝ) * (g 1 1 : ℝ)) ∘ has_smul.smul (⟨(g 1 0 : ℝ) * (g 1 0 : ℝ), h1⟩ : {x : ℝ // (0 : ℝ)
  < x})) z :=
begin
  obtain ⟨a, b, c, d, h, hg⟩ := g.fin_two_exists_eq_mk,
  have hg00 : g 0 0 = a := by rw [hg]; refl,
  have hg01 : g 0 1 = b := by rw [hg]; refl,
  have hg10 : g 1 0 = c := by rw [hg]; refl,
  have hg11 : g 1 1 = d := by rw [hg]; refl,
  have hg00' := hg00,
  have hg01' := hg01,
  have hg10' := hg10,
  have hg11' := hg11,
  rw matrix.special_linear_group.coe_fn_eq_coe at hg00',
  rw matrix.special_linear_group.coe_fn_eq_coe at hg01',
  rw matrix.special_linear_group.coe_fn_eq_coe at hg10',
  rw matrix.special_linear_group.coe_fn_eq_coe at hg11',
  have hg := g.property,
  rw [subtype.val_eq_coe, matrix.det_fin_two] at hg,
  have hg' : (a * d - b * c : ℂ) = (1 : ℂ), norm_cast, assumption,
  rw hg10 at h1,
  rw [subtype.ext_iff, special_linear_group_apply g z],
  simp [involute_apply],
  rw [mul_assoc, ← neg_mul, ← neg_mul, ← mul_add],
  rw [hg00', hg01', hg10', hg11'],
  have h2 := h1, rw mul_self_pos at h2,
  have h2' : (c : ℂ) ≠ (0 : ℂ), by_contra, apply h2, norm_cast at h,
  have h4 : (c : ℂ) * z + (d : ℂ) ≠ 0,
  have h4' : denom g z = ((g 1 0) : ℂ) * z + ((g 1 1) : ℂ) := rfl,
  rw [hg10, hg11] at h4',
  rw ← h4', refine denom_ne_zero g _,
  have h5 : -(c : ℂ) * ((c : ℂ) * z + (d : ℂ)) ≠ 0, have h5' : -(c : ℂ) ≠ (0 : ℂ),
  exact neg_ne_zero.mpr h2', positivity,
  field_simp,
  linear_combination (↑z * ↑c ^ 2 + ↑c * ↑d) * hg',
end

@[simp] lemma dist_SL2_smul_smul (g : SL(2, ℝ)) (z w : ℍ) :
  dist (g • z) (g • w) = dist z w :=
begin
  obtain ⟨a, b, c, d, h, hg⟩ := g.fin_two_exists_eq_mk,
  have hg00 : g 0 0 = a := by rw [hg]; refl,
  have hg01 : g 0 1 = b := by rw [hg]; refl,
  have hg10 : g 1 0 = c := by rw [hg]; refl,
  have hg11 : g 1 1 = d := by rw [hg]; refl,
  have hg00' := hg00,
  have hg01' := hg01,
  have hg10' := hg10,
  have hg11' := hg11,
  rw matrix.special_linear_group.coe_fn_eq_coe at hg00',
  rw matrix.special_linear_group.coe_fn_eq_coe at hg01',
  rw matrix.special_linear_group.coe_fn_eq_coe at hg10',
  rw matrix.special_linear_group.coe_fn_eq_coe at hg11',
  have h : 0 ≤ c * c, exact mul_self_nonneg _,
  have h1 := eq_or_lt_of_le h, clear h,
  have hg := g.property,
  rw [subtype.val_eq_coe, matrix.det_fin_two] at hg,
  have hg' : (a * d - b * c : ℂ) = (1 : ℂ), norm_cast, assumption,
  cases h1 with h1 h1,
  { rw zero_eq_mul_self at h1,
    rw ← hg10 at h1,
    exact dist_SL2_smul_smul_c_zero g z w h1, },
  { have h2 : (c : ℝ) ≠ (0 : ℝ), rw ← mul_self_pos, exact h1,
    have h2' : (c : ℂ) ≠ (0 : ℂ), by_contra, apply h2, norm_cast at h,
    rw ← hg10 at h1,
    have h3 := isometry.comp (isometry_real_vadd ((g 0 0 : ℝ) / (g 1 0 : ℝ)))
    (isometry.comp isometry_involute (isometry.comp(isometry_real_vadd ((g 1 0 : ℝ)
    * (g 1 1 : ℝ))) (isometry_pos_mul ⟨(g 1 0 : ℝ) * (g 1 0 : ℝ), h1⟩))),
    rw isometry_iff_dist_eq at h3,
    specialize h3 z w,
    convert h3,
    { exact dist_SL2_eq_comp_c_nonzero _ _ _, },
    { exact dist_SL2_eq_comp_c_nonzero _ _ _, }, },
end

end upper_half_plane
