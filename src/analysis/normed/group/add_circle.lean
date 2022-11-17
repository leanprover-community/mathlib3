/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import analysis.normed.group.quotient
import topology.instances.add_circle

/-!
# The additive circle as a normed group

We define the normed group structure on `add_circle p`, for `p : ℝ`. For example if `p = 1` then:
`∥(x : add_circle 1)∥ = |x - round x|` for any `x : ℝ` (see `unit_add_circle.norm_eq`).

## Main definitions:

 * `add_circle.norm_eq`: a characterisation of the norm on `add_circle p`

## TODO

 * The fact `inner_product_geometry.angle (real.cos θ) (real.sin θ) = ∥(θ : real.angle)∥`

-/

noncomputable theory

open set int (hiding mem_zmultiples_iff) add_subgroup

namespace add_circle

variables (p : ℝ)

instance : normed_add_comm_group (add_circle p) := add_subgroup.normed_add_comm_group_quotient _

@[simp] lemma norm_coe_mul (x : ℝ) (t : ℝ) :
  ∥(↑(t * x) : add_circle (t * p))∥ = |t| * ∥(x : add_circle p)∥ :=
begin
  have aux : ∀ {a b c : ℝ}, a ∈ zmultiples b → c * a ∈ zmultiples (c * b) := λ a b c h, by
  { simp only [mem_zmultiples_iff] at ⊢ h,
    obtain ⟨n, rfl⟩ := h,
    exact ⟨n, (mul_smul_comm n c b).symm⟩, },
  rcases eq_or_ne t 0 with rfl | ht, { simp, },
  have ht' : |t| ≠ 0 := (not_congr abs_eq_zero).mpr ht,
  simp only [quotient_norm_eq, real.norm_eq_abs],
  conv_rhs { rw [← smul_eq_mul, ← real.Inf_smul_of_nonneg (abs_nonneg t)], },
  simp only [quotient_add_group.mk'_apply, quotient_add_group.eq_iff_sub_mem],
  congr' 1,
  ext z,
  rw mem_smul_set_iff_inv_smul_mem₀ ht',
  show (∃ y, y - t * x ∈ zmultiples (t * p) ∧ |y| = z) ↔ ∃w, w - x ∈ zmultiples p ∧ |w| = |t|⁻¹ * z,
  split,
  { rintros ⟨y, hy, rfl⟩,
    refine ⟨t⁻¹ * y, _, by rw [abs_mul, abs_inv]⟩,
    rw [← inv_mul_cancel_left₀ ht x, ← inv_mul_cancel_left₀ ht p, ← mul_sub],
    exact aux hy, },
  { rintros ⟨w, hw, hw'⟩,
    refine ⟨t * w, _, by rw [← (eq_inv_mul_iff_mul_eq₀ ht').mp hw', abs_mul]⟩,
    rw ← mul_sub,
    exact aux hw, },
end

lemma norm_neg_period (x : ℝ) :
  ∥(x : add_circle (-p))∥ = ∥(x : add_circle p)∥ :=
begin
  suffices : ∥(↑(-1 * x) : add_circle (-1 * p))∥ = ∥(x : add_circle p)∥,
  { rw [← this, neg_one_mul], simp, },
  simp only [norm_coe_mul, abs_neg, abs_one, one_mul],
end

@[simp] lemma norm_eq_of_zero {x : ℝ} : ∥(x : add_circle (0 : ℝ))∥ = |x| :=
begin
  suffices : {y : ℝ | (y : add_circle (0 : ℝ)) = (x : add_circle (0 : ℝ)) } = { x },
  { rw [quotient_norm_eq, this, image_singleton, real.norm_eq_abs, cInf_singleton], },
  ext y,
  simp [quotient_add_group.eq_iff_sub_mem, mem_zmultiples_iff, sub_eq_zero],
end

lemma norm_eq {x : ℝ} : ∥(x : add_circle p)∥ = |x - round (p⁻¹ * x) * p| :=
begin
  suffices : ∀ (x : ℝ), ∥(x : add_circle (1 : ℝ))∥ = |x - round x|,
  { rcases eq_or_ne p 0 with rfl | hp, { simp, },
    intros,
    have hx := norm_coe_mul p x p⁻¹,
    rw [abs_inv, eq_inv_mul_iff_mul_eq₀ ((not_congr abs_eq_zero).mpr hp)] at hx,
    rw [← hx, inv_mul_cancel hp, this, ← abs_mul, mul_sub, mul_inv_cancel_left₀ hp, mul_comm p], },
  clear x p,
  intros,
  rw [quotient_norm_eq, abs_sub_round_eq_min],
  have h₁ : bdd_below (abs '' {m : ℝ | (m : add_circle (1 : ℝ)) = x}) :=
    ⟨0, by simp [mem_lower_bounds]⟩,
  have h₂ : (abs '' {m : ℝ | (m : add_circle (1 : ℝ)) = x}).nonempty := ⟨|x|, ⟨x, rfl, rfl⟩⟩,
  apply le_antisymm,
  { simp only [le_min_iff, real.norm_eq_abs, cInf_le_iff h₁ h₂],
    intros b h,
    refine ⟨mem_lower_bounds.1 h _ ⟨fract x, _, abs_fract⟩,
            mem_lower_bounds.1 h _ ⟨fract x - 1, _, by rw [abs_sub_comm, abs_one_sub_fract]⟩⟩,
    { simp only [mem_set_of_eq, fract, sub_eq_self, quotient_add_group.coe_sub,
        quotient_add_group.eq_zero_iff, int_cast_mem_zmultiples_one], },
    { simp only [mem_set_of_eq, fract, sub_eq_self, quotient_add_group.coe_sub,
        quotient_add_group.eq_zero_iff, int_cast_mem_zmultiples_one, sub_sub,
        (by norm_cast : (⌊x⌋ : ℝ) + 1 = (↑(⌊x⌋ + 1) : ℝ))], }, },
  { simp only [quotient_add_group.mk'_apply, real.norm_eq_abs, le_cInf_iff h₁ h₂],
    rintros b' ⟨b, hb, rfl⟩,
    simp only [mem_set_of_eq, quotient_add_group.eq_iff_sub_mem, mem_zmultiples_iff,
      smul_one_eq_coe] at hb,
    obtain ⟨z, hz⟩ := hb,
    rw [(by { rw hz, abel, } : x = b - z), fract_sub_int, ← abs_sub_round_eq_min],
    convert round_le b 0,
    simp, },
end

lemma norm_le_half_period {x : add_circle p} (hp : p ≠ 0) : ∥x∥ ≤ |p|/2 :=
begin
  obtain ⟨x⟩ := x,
  change ∥(x : add_circle p)∥ ≤ |p|/2,
  rw [norm_eq, ← mul_le_mul_left (abs_pos.mpr (inv_ne_zero hp)), ← abs_mul, mul_sub, mul_left_comm,
    ← mul_div_assoc, ← abs_mul, inv_mul_cancel hp, mul_one, abs_one],
  exact abs_sub_round (p⁻¹ * x),
end

@[simp] lemma norm_half_period_eq : ∥(↑(p/2) : add_circle p)∥ = |p|/2 :=
begin
  rcases eq_or_ne p 0 with rfl | hp, { simp, },
  rw [norm_eq, ← mul_div_assoc, inv_mul_cancel hp, one_div, round_two_inv, algebra_map.coe_one,
    one_mul, (by linarith : p / 2 - p = -(p / 2)), abs_neg, abs_div, abs_two],
end

lemma norm_coe_eq_abs_iff {x : ℝ} (hp : p ≠ 0) : ∥(x : add_circle p)∥ = |x| ↔ |x| ≤ |p|/2 :=
begin
  refine ⟨λ hx, hx ▸ norm_le_half_period p hp, λ hx, _⟩,
  suffices : ∀ (p : ℝ), 0 < p → |x| ≤ p/2 → ∥(x : add_circle p)∥ = |x|,
  { rcases lt_trichotomy 0 p with hp | rfl | hp,
    { rw abs_eq_self.mpr hp.le at hx,
      exact this p hp hx, },
    { contradiction, },
    { rw ← norm_neg_period,
      rw abs_eq_neg_self.mpr hp.le at hx,
      exact this (-p) (neg_pos.mpr hp) hx, }, },
  clear hx,
  intros p hp hx,
  rcases eq_or_ne x (p/2) with rfl | hx', { simp [abs_div, abs_two], },
  suffices : round (p⁻¹ * x) = 0, { simp [norm_eq, this], },
  rw round_eq_zero_iff,
  obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx,
  replace hx₂ := ne.lt_of_le hx' hx₂,
  split,
  { rwa [← mul_le_mul_left hp, ← mul_assoc, mul_inv_cancel hp.ne.symm, one_mul, mul_neg,
      ← mul_div_assoc, mul_one], },
  { rwa [← mul_lt_mul_left hp, ← mul_assoc, mul_inv_cancel hp.ne.symm, one_mul, ← mul_div_assoc,
      mul_one], },
end

open metric

lemma closed_ball_eq_univ_of_half_period_le
  (hp : p ≠ 0) (x : add_circle p) {ε : ℝ} (hε : |p|/2 ≤ ε) :
  closed_ball x ε = univ :=
eq_univ_iff_forall.mpr $
  λ x, by simpa only [mem_closed_ball, dist_eq_norm] using (norm_le_half_period p hp).trans hε

@[simp] lemma coe_real_preimage_closed_ball_period_zero (x ε : ℝ) :
  coe⁻¹' closed_ball (x : add_circle (0 : ℝ)) ε = closed_ball x ε :=
by { ext y; simp [dist_eq_norm, ← quotient_add_group.coe_sub], }

lemma coe_real_preimage_closed_ball_eq_Union (x ε : ℝ) :
  coe⁻¹' closed_ball (x : add_circle p) ε = ⋃ (z : ℤ), closed_ball (x + z • p) ε :=
begin
  rcases eq_or_ne p 0 with rfl | hp, { simp [Union_const], },
  ext y,
  simp only [dist_eq_norm, mem_preimage, mem_closed_ball, zsmul_eq_mul, mem_Union, real.norm_eq_abs,
    ← quotient_add_group.coe_sub, norm_eq, ← sub_sub],
  refine ⟨λ h, ⟨round (p⁻¹ * (y - x)), h⟩, _⟩,
  rintros ⟨n, hn⟩,
  rw [← mul_le_mul_left (abs_pos.mpr $ inv_ne_zero hp), ← abs_mul, mul_sub, mul_comm _ p,
    inv_mul_cancel_left₀ hp] at hn ⊢,
  exact (round_le (p⁻¹ * (y - x)) n).trans hn,
end

lemma coe_real_preimage_closed_ball_inter_eq
  {x ε : ℝ} (s : set ℝ) (hs : s ⊆ closed_ball x (|p|/2)) :
  coe⁻¹' closed_ball (x : add_circle p) ε ∩ s = if ε < |p|/2 then (closed_ball x ε) ∩ s else s :=
begin
  cases le_or_lt (|p|/2) ε with hε hε,
  { rcases eq_or_ne p 0 with rfl | hp,
    { simp only [abs_zero, zero_div] at hε,
      simp only [not_lt.mpr hε, coe_real_preimage_closed_ball_period_zero, abs_zero, zero_div,
        if_false, inter_eq_right_iff_subset],
      exact hs.trans (closed_ball_subset_closed_ball $ by simp [hε]), },
    simp [closed_ball_eq_univ_of_half_period_le p hp ↑x hε, not_lt.mpr hε], },
  { suffices : ∀ (z : ℤ), closed_ball (x + z • p) ε ∩ s = if z = 0 then closed_ball x ε ∩ s else ∅,
    { simp [-zsmul_eq_mul, ← quotient_add_group.coe_zero, coe_real_preimage_closed_ball_eq_Union,
        Union_inter, Union_ite, this, hε], },
    intros z,
    simp only [real.closed_ball_eq_Icc, zero_sub, zero_add] at ⊢ hs,
    rcases eq_or_ne z 0 with rfl | hz, { simp, },
    simp only [hz, zsmul_eq_mul, if_false, eq_empty_iff_forall_not_mem],
    rintros y ⟨⟨hy₁, hy₂⟩, hy₀⟩,
    obtain ⟨hy₃, hy₄⟩ := hs hy₀,
    rcases lt_trichotomy 0 p with hp | rfl | hp,
    { cases int.cast_le_neg_one_or_one_le_cast_of_ne_zero ℝ hz with hz' hz',
      { have : ↑z * p ≤ - p, nlinarith,
        linarith [abs_eq_self.mpr hp.le] },
      { have : p ≤ ↑z * p, nlinarith,
        linarith [abs_eq_self.mpr hp.le] } },
    { simp only [mul_zero, add_zero, abs_zero, zero_div] at hy₁ hy₂ hε,
      linarith },
    { cases int.cast_le_neg_one_or_one_le_cast_of_ne_zero ℝ hz with hz' hz',
      { have : - p ≤ ↑z * p, nlinarith,
        linarith [abs_eq_neg_self.mpr hp.le] },
      { have : ↑z * p ≤ p, nlinarith,
        linarith [abs_eq_neg_self.mpr hp.le] } } },
end

end add_circle

namespace unit_add_circle

lemma norm_eq {x : ℝ} : ∥(x : unit_add_circle)∥ = |x - round x| := by simp [add_circle.norm_eq]

end unit_add_circle
