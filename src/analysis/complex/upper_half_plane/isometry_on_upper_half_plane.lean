/-
Copyright (c) 2023 Oliver Nash, Wan Ruizhe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Wan Ruizhe
-/
import analysis.complex.upper_half_plane.metric
import analysis.complex.upper_half_plane.basic
import tactic.linear_combination

/-!
This file proves that every element in SL2 acts on the upper half-plane as an isometry.

-/

noncomputable theory

namespace upper_half_plane

open_locale upper_half_plane matrix_groups

instance : has_smul {A : matrix (fin 2) (fin 2) ℝ // matrix.det A = 1} ℍ :=
upper_half_plane.SL_action.to_has_smul

open_locale matrix_groups
local notation `GL(` n `, ` R `)`⁺ := matrix.GL_pos (fin n) R

@[simp] lemma coe_SL2_apply (a b c d : ℝ) (h) (z : ℍ) :
  (↑((⟨!![a, b; c, d], h⟩ : SL(2, ℝ)) • z) : ℂ) = (a * z + b) / (c * z + d) :=
rfl

@[simp] lemma SL2_apply (a b c d : ℝ) (h) (z : ℍ) :
  ((⟨!![a, b; c, d], h⟩ : SL(2, ℝ)) • z) = ⟨(a * (z : ℂ) + b) / (c * (z : ℂ) + d),
  ((⟨!![a, b; c, d], h⟩ : SL(2, ℝ)) • z).property⟩ :=
rfl

/-- An element of `SL(2, ℝ)` representing the Mobiüs transformation `z ↦ -1/z`.

This defines an involutive elliptic isometry of the hyperbolic plane, fixing `i` and rotating
(hyperbolically) by `π`.
-/
def involute : SL(2, ℝ) := ⟨!![0, -1; 1, 0], by norm_num [matrix.det_fin_two_of]⟩

@[simp, norm_cast] lemma coe_involute (z : ℍ) : (↑(involute • z) : ℂ) = (-z : ℂ)⁻¹ :=
begin
  simp [involute, neg_div, inv_neg],
end

@[simp] lemma im_mk (z : ℂ) (h) : im (⟨z, h⟩ : ℍ) = z.im := rfl

@[simp] lemma im_involute_smul (z : ℍ) : (involute • z).im = z.im / (z : ℂ).norm_sq :=
by { obtain ⟨z, hz⟩ := z, simp [involute, neg_div], }

lemma SL2_apply_aux (a b c d : ℝ) (h : matrix.det !![a, b; c, d] = 1) (z : ℍ) :
  0 < ((↑a * (z : ℂ) + b) / (↑c * (z : ℂ) + d)).im :=
((⟨!![a, b; c, d], h⟩ : SL(2, ℝ)) • z).property

lemma div_sq {z w : ℝ} : (z / w)^2 = z^2 / w^2 :=
by simp only [div_eq_mul_inv, sq, mul_mul_mul_comm z w⁻¹, mul_inv]

lemma mul_sq {z w : ℝ} : (z * w)^2 = z^2 * w^2 :=
by simp only [sq, mul_mul_mul_comm z w]

lemma isometry_involute : isometry (λ z, involute • z : ℍ → ℍ) :=
begin
  refine isometry.of_dist_eq _,
  rintros ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩,
  simp only [dist_eq],
  congr' 2,
  refine (mul_self_inj _ _).mp _,
  { positivity, },
  { positivity, },
  simp only [← sq, div_sq, mul_sq],
  have h1: 0 ≤ y₁.re*y₁.re, exact mul_self_nonneg _,
  have h2: 0 ≤ y₂.re*y₂.re, exact mul_self_nonneg _,
  have h3: 0 ≤ (-y₁).re*(-y₁).re, exact mul_self_nonneg _,
  have h4: 0 ≤ (-y₂).re*(-y₂).re, exact mul_self_nonneg _,
  have h5: 0 < (-y₁).im*(-y₁).im, rw [complex.neg_im, mul_self_pos, neg_ne_zero],
  exact ne_of_gt hy₁,
  have h6: 0 < (-y₂).im*(-y₂).im, rw [complex.neg_im, mul_self_pos, neg_ne_zero],
  exact ne_of_gt hy₂,
  have h7: 0 ≤ (y₁-y₂).re*(y₁-y₂).re, exact mul_self_nonneg _,
  have h8: 0 ≤ (y₁-y₂).im*(y₁-y₂).im, exact mul_self_nonneg _,
  have h9: 0 ≤ ((-y₁)⁻¹ - (-y₂)⁻¹).re * ((-y₁)⁻¹ - (-y₂)⁻¹).re, exact mul_self_nonneg _,
  have h10: 0 ≤ ((-y₁)⁻¹ - (-y₂)⁻¹).im * ((-y₁)⁻¹ - (-y₂)⁻¹).im, exact mul_self_nonneg _,
  rw [real.sq_sqrt _, real.sq_sqrt _],
  { simp only [coe_involute, subtype.coe_mk, im_involute_smul, im_mk, complex.dist_eq,
    complex.abs],
    simp only [absolute_value.coe_mk, mul_hom.coe_mk],
    rw [real.sq_sqrt _, real.sq_sqrt _],
    {refine (div_eq_div_iff _ _).mp _,
    {positivity,},
    {apply inv_ne_zero,
    rw mul_ne_zero_iff,
    split, {norm_num,},
    rw mul_ne_zero_iff,
    split,
    {rw div_ne_zero_iff,
    split, {positivity,},
    {simp only [complex.norm_sq_apply],
    positivity,}},
    {rw div_ne_zero_iff,
    split, {positivity,},
    {simp only [complex.norm_sq_apply],
    positivity,}},},
    rw [div_inv_eq_mul, div_inv_eq_mul],
    simp only [complex.norm_sq_apply],
    simp only [complex.sub_re, complex.sub_im, complex.inv_re, complex.inv_im,
    complex.norm_sq_apply],
    rw [div_sub_div, div_sub_div],
    {have h11: (((-y₁).re * (-y₁).re + (-y₁).im * (-y₁).im) *
    ((-y₂).re * (-y₂).re + (-y₂).im * (-y₂).im))≠0,
    positivity,
    have h12: ((y₁.re * y₁.re + y₁.im * y₁.im) * (y₂.re * y₂.re + y₂.im * y₂.im) *
    ((y₁.re * y₁.re + y₁.im * y₁.im) * (y₂.re * y₂.re + y₂.im * y₂.im)))≠0,
    positivity,
    have h13: ((y₁.re * y₁.re + y₁.im * y₁.im) * (y₂.re * y₂.re + y₂.im * y₂.im))≠0,
    positivity,
    field_simp,
    ring,},
    {positivity,},
    {positivity,},
    {positivity,},
    {positivity,}},
    {simp only [complex.norm_sq_apply],
    positivity,},
    {simp only [complex.norm_sq_apply],
    positivity,},},
  { positivity,},
  { have h11: (0 : ℝ) < (involute • ⟨y₁, hy₁⟩ : ℍ).im := (involute • ⟨y₁, hy₁⟩ : ℍ).property,
  have h12: (0 : ℝ) < (involute • ⟨y₂, hy₂⟩ : ℍ).im := (involute • ⟨y₂, hy₂⟩ : ℍ).property,
  positivity,},
end

lemma transform_denom_apply (g : SL(2, ℝ)) (z : ℍ): denom g z = ((g 1 0) : ℂ) * z + ((g 1 1) : ℂ)
  := by refl

@[simp] lemma coe_SL2 (g : SL(2, ℝ)) (z : ℍ): ↑ (g • z) = (((g 0 0) : ℂ) * z + ((g 0 1) : ℂ)) /
  (((g 1 0) : ℂ) * z + ((g 1 1) : ℂ)) :=
begin
have h1 : ↑ (g • z) = num g z / denom g z, refl,
have h2 : num g z = ((g 0 0) : ℂ) * z + ((g 0 1) : ℂ), refl,
rw [h1, h2, transform_denom_apply],
end

lemma SL2_exists_abcd (g : SL(2, ℝ)) :
  ∃ (a b c d : ℝ) (h : a * d - b * c = 1), g = (⟨!![a, b; c, d], by rwa [matrix.det_fin_two_of]⟩
  : SL(2, ℝ)) :=
begin
  refine ⟨g 0 0, g 0 1, g 1 0, g 1 1, _, _⟩,
  { erw ← g.val.det_fin_two, simp, },
  { ext i j, fin_cases i; fin_cases j; refl, },
end

lemma dist_SL2_smul_smul_c_zero (g : SL(2, ℝ)) (z w : ℍ) (h1 : g 1 0 = 0) :
  dist (g • z) (g • w) = dist z w :=
begin
  obtain ⟨a, b, c, d, h, hg⟩ := SL2_exists_abcd g,
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
    simp only [← sq, div_sq, mul_sq],
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
      { rw [← coe_im (g • z), ← coe_im (g • w)],
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
  obtain ⟨a, b, c, d, h, hg⟩ := SL2_exists_abcd g,
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
  rw subtype.ext_iff,
  simp [coe_involute],
  rw [mul_assoc, ← neg_mul, ← neg_mul, ← mul_add],
  rw [hg00', hg01', hg10', hg11'],
  have h2 := h1, rw mul_self_pos at h2,
  have h2' : (c : ℂ) ≠ (0 : ℂ), by_contra, apply h2, norm_cast at h,
  have h4 : (c : ℂ) * z + (d : ℂ) ≠ 0, have h4' := transform_denom_apply g z,
  rw [hg10, hg11] at h4',
  rw ← h4', refine denom_ne_zero (g : GL(2, ℝ)⁺) _,
  have h5 : -(c : ℂ) * ((c : ℂ) * z + (d : ℂ)) ≠ 0, have h5' : -(c : ℂ) ≠ (0 : ℂ),
  exact neg_ne_zero.mpr h2', positivity,
  field_simp,
  linear_combination (↑z * ↑c ^ 2 + ↑c * ↑d) * hg',
end

@[simp] lemma dist_SL2_smul_smul (g : SL(2, ℝ)) (z w : ℍ) :
  dist (g • z) (g • w) = dist z w :=
begin
  obtain ⟨a, b, c, d, h, hg⟩ := SL2_exists_abcd g,
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
