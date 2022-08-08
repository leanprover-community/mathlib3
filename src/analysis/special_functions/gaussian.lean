/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.special_functions.gamma
import analysis.special_functions.polar_coord

/-!
# Gaussian integral

We prove the formula `∫ x, exp (-b * x^2) = sqrt (π / b)`, in `integral_gaussian`.
-/

noncomputable theory

open real set measure_theory filter asymptotics
open_locale real topological_space

lemma exp_neg_mul_sq_is_o_exp_neg {b : ℝ} (hb : 0 < b) :
  (λ x:ℝ, exp (-b * x^2)) =o[at_top] (λ x:ℝ, exp (-x)) :=
begin
  have A : (λ (x : ℝ), -x - -b * x ^ 2) = (λ x, x * (b * x + (- 1))), by { ext x, ring },
  rw [is_o_exp_comp_exp_comp, A],
  apply tendsto.at_top_mul_at_top tendsto_id,
  apply tendsto_at_top_add_const_right at_top (-1 : ℝ),
  exact tendsto.const_mul_at_top hb tendsto_id,
end

lemma rpow_mul_exp_neg_mul_sq_is_o_exp_neg {b : ℝ} (hb : 0 < b) (s : ℝ) :
  (λ x:ℝ, x ^ s * exp (-b * x^2)) =o[at_top] (λ x:ℝ, exp (-(1/2) * x)) :=
begin
  apply ((is_O_refl (λ x:ℝ, x ^ s) at_top).mul_is_o (exp_neg_mul_sq_is_o_exp_neg hb)).trans,
  convert Gamma_integrand_is_o s,
  simp_rw [mul_comm],
end

lemma integrable_on_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
  integrable_on (λ x:ℝ, x ^ s * exp (-b * x^2)) (Ioi 0) :=
begin
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrable_on_union],
  split,
  { rw [←integrable_on_Icc_iff_integrable_on_Ioc],
    refine integrable_on.mul_continuous_on _ _ is_compact_Icc,
    { refine (interval_integrable_iff_integrable_Icc_of_le zero_le_one).mp _,
      exact interval_integral.interval_integrable_rpow' hs },
    { exact (continuous_exp.comp (continuous_const.mul (continuous_pow 2))).continuous_on } },
  { have B : (0 : ℝ) < 1/2, by norm_num,
    apply integrable_of_is_O_exp_neg B _ (is_o.is_O (rpow_mul_exp_neg_mul_sq_is_o_exp_neg hb _)),
    assume x hx,
    have N : x ≠ 0, { refine (zero_lt_one.trans_le _).ne', exact hx },
    apply ((continuous_at_rpow_const _ _ (or.inl N)).mul _).continuous_within_at,
    exact (continuous_exp.comp (continuous_const.mul (continuous_pow 2))).continuous_at },
end

lemma integrable_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
  integrable (λ x:ℝ, x ^ s * exp (-b * x^2)) :=
begin
  rw [← integrable_on_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrable_on_union,
      integrable_on_Ici_iff_integrable_on_Ioi],
  refine ⟨_, integrable_on_rpow_mul_exp_neg_mul_sq hb hs⟩,
  rw ← (measure.measure_preserving_neg (volume : measure ℝ)).integrable_on_comp_preimage
    ((homeomorph.neg ℝ).to_measurable_equiv.measurable_embedding),
  simp only [function.comp, neg_sq, neg_preimage, preimage_neg_Iio, neg_neg, neg_zero],
  apply integrable.mono' (integrable_on_rpow_mul_exp_neg_mul_sq hb hs),
  { apply measurable.ae_strongly_measurable,
    exact (measurable_id'.neg.pow measurable_const).mul
      ((measurable_id'.pow measurable_const).const_mul (-b)).exp },
  { have : measurable_set (Ioi (0 : ℝ)) := measurable_set_Ioi,
    filter_upwards [ae_restrict_mem this] with x hx,
    have h'x : 0 ≤ x := le_of_lt hx,
    rw [real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_pos _).le],
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le,
    simpa [abs_of_nonneg h'x] using abs_rpow_le_abs_rpow (-x) s }
end

lemma integrable_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
  integrable (λ x:ℝ, exp (-b * x^2)) :=
begin
  have A : (-1 : ℝ) < 0, by norm_num,
  convert integrable_rpow_mul_exp_neg_mul_sq hb A,
  simp,
end

lemma integrable_exp_neg_mul_sq_iff {b : ℝ} :
  integrable (λ x:ℝ, exp (-b * x^2)) ↔ 0 < b :=
begin
  refine ⟨λ h, _, integrable_exp_neg_mul_sq⟩,
  by_contra' hb,
  have : ∫⁻ x:ℝ, 1 ≤ ∫⁻ x:ℝ, ∥exp (-b * x^2)∥₊,
  { apply lintegral_mono (λ x, _),
    simp only [neg_mul, ennreal.one_le_coe_iff, ← to_nnreal_one, to_nnreal_le_iff_le_coe,
      real.norm_of_nonneg (exp_pos _).le, coe_nnnorm, one_le_exp_iff, right.nonneg_neg_iff],
    exact mul_nonpos_of_nonpos_of_nonneg hb (sq_nonneg _) },
  simpa using this.trans_lt h.2,
end

lemma integrable_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
  integrable (λ x:ℝ, x * exp (-b * x^2)) :=
begin
  have A : (-1 : ℝ) < 1, by norm_num,
  convert integrable_rpow_mul_exp_neg_mul_sq hb A,
  simp,
end

lemma integral_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
  ∫ r in Ioi 0, r * exp (-b * r ^ 2) = (2 * b)⁻¹ :=
begin
  have I : integrable (λ x, x * exp (-b * x^2)) := integrable_mul_exp_neg_mul_sq hb,
  refine tendsto_nhds_unique
    (interval_integral_tendsto_integral_Ioi _ I.integrable_on filter.tendsto_id) _,
  have A : ∀ x, has_deriv_at (λ x, - (2 * b)⁻¹ * exp (-b * x^2)) (x * exp (- b * x^2)) x,
  { assume x,
    convert (((has_deriv_at_pow 2 x)).const_mul (-b)).exp.const_mul (- (2 * b)⁻¹) using 1,
    field_simp [hb.ne'],
    ring },
  have : ∀ (y : ℝ), ∫ x in 0..(id y), x * exp (- b * x^2)
      = (- (2 * b)⁻¹ * exp (-b * y^2)) - (- (2 * b)⁻¹ * exp (-b * 0^2)) :=
    λ y, interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx, A x) I.interval_integrable,
  simp_rw [this],
  have L : tendsto (λ (x : ℝ), (2 * b)⁻¹ - (2 * b)⁻¹ * exp (-b * x ^ 2)) at_top
    (𝓝 ((2 * b)⁻¹ - (2 * b)⁻¹ * 0)),
  { refine tendsto_const_nhds.sub _,
    apply tendsto.const_mul,
    apply tendsto_exp_at_bot.comp,
    exact tendsto.neg_const_mul_at_top (neg_lt_zero.2 hb) (tendsto_pow_at_top two_ne_zero) },
  simpa using L,
end

theorem integral_gaussian (b : ℝ) : ∫ x, exp (-b * x^2) = sqrt (π / b) :=
begin
  /- First we deal with the crazy case where `b ≤ 0`: then both sides vanish. -/
  rcases le_or_lt b 0 with hb|hb,
  { rw [integral_undef, sqrt_eq_zero_of_nonpos],
    { exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb },
    { simpa only [not_lt, integrable_exp_neg_mul_sq_iff] using hb } },
  /- Assume now `b > 0`. We will show that the squares of the sides coincide. -/
  refine (sq_eq_sq _ (sqrt_nonneg _)).1 _,
  { exact integral_nonneg (λ x, (exp_pos _).le) },
  /- We compute `(∫ exp(-b x^2))^2` as an integral over `ℝ^2`, and then make a polar change of
  coordinates. We are left with `∫ r * exp (-b r^2)`, which has been computed in
  `integral_mul_exp_neg_mul_sq` using the fact that this function has an obvious primitive. -/
  calc
  (∫ x, real.exp (-b * x^2)) ^ 2
      = ∫ p : ℝ × ℝ, exp (-b * p.1 ^ 2) * exp (-b * p.2 ^ 2) :
    by { rw [pow_two, ← integral_prod_mul], refl }
  ... = ∫ p : ℝ × ℝ, real.exp (- b * (p.1 ^ 2 + p.2^2)) :
    by { congr, ext p, simp only [← real.exp_add, neg_add_rev, real.exp_eq_exp], ring }
  ... = ∫ p in polar_coord.target, p.1 * exp (- b * ((p.1 * cos p.2) ^ 2 + (p.1 * sin p.2)^2)) :
    (integral_comp_polar_coord_symm (λ p, exp (- b * (p.1^2 + p.2^2)))).symm
  ... = (∫ r in Ioi (0 : ℝ), r * exp (-b * r^2)) * (∫ θ in Ioo (-π) π, 1) :
    begin
      rw ← set_integral_prod_mul,
      congr' with p,
      rw mul_one,
      congr,
      conv_rhs { rw [← one_mul (p.1^2), ← sin_sq_add_cos_sq p.2], },
      ring_exp,
    end
  ... = π / b :
    begin
      have : 0 ≤ π + π, by linarith [real.pi_pos],
      simp only [integral_const, measure.restrict_apply', measurable_set_Ioo, univ_inter, this,
          sub_neg_eq_add, algebra.id.smul_eq_mul, mul_one, volume_Ioo, two_mul,
          ennreal.to_real_of_real, integral_mul_exp_neg_mul_sq hb, one_mul],
      field_simp [hb.ne'],
      ring,
    end
  ... = (sqrt (π / b)) ^ 2 :
    by { rw sq_sqrt, exact div_nonneg pi_pos.le hb.le }
end
