/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.special_functions.gamma
import analysis.special_functions.polar_coord
import analysis.convex.complex

/-!
# Gaussian integral

We prove various versions of the formula for the Gaussian integral:
* `integral_gaussian`: for real `b` we have `∫ x:ℝ, exp (-b * x^2) = sqrt (π / b)`.
* `integral_gaussian_complex`: for complex `b` with `0 < re b` we have
  `∫ x:ℝ, exp (-b * x^2) = (π / b) ^ (1 / 2)`.
* `integral_gaussian_Ioi` and `integral_gaussian_complex_Ioi`: variants for integrals over `Ioi 0`.
* `complex.Gamma_one_half_eq`: the formula `Γ (1 / 2) = √π`.
-/

noncomputable theory

open real set measure_theory filter asymptotics
open_locale real topological_space

open complex (hiding exp continuous_exp abs_of_nonneg)
notation `cexp` := complex.exp

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
by simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 0)

lemma integrable_on_Ioi_exp_neg_mul_sq_iff {b : ℝ} :
  integrable_on (λ x:ℝ, exp (-b * x^2)) (Ioi 0) ↔ 0 < b :=
begin
  refine ⟨λ h, _, λ h, (integrable_exp_neg_mul_sq h).integrable_on⟩,
  by_contra' hb,
  have : ∫⁻ x:ℝ in Ioi 0, 1 ≤ ∫⁻ x:ℝ in Ioi 0, ‖exp (-b * x^2)‖₊,
  { apply lintegral_mono (λ x, _),
    simp only [neg_mul, ennreal.one_le_coe_iff, ← to_nnreal_one, to_nnreal_le_iff_le_coe,
      real.norm_of_nonneg (exp_pos _).le, coe_nnnorm, one_le_exp_iff, right.nonneg_neg_iff],
    exact mul_nonpos_of_nonpos_of_nonneg hb (sq_nonneg _) },
  simpa using this.trans_lt h.2,
end

lemma integrable_exp_neg_mul_sq_iff {b : ℝ} : integrable (λ x:ℝ, exp (-b * x^2)) ↔ 0 < b :=
⟨λ h, integrable_on_Ioi_exp_neg_mul_sq_iff.mp h.integrable_on, integrable_exp_neg_mul_sq⟩

lemma integrable_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) : integrable (λ x:ℝ, x * exp (-b * x^2)) :=
by simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 1)

lemma norm_cexp_neg_mul_sq (b : ℂ) (x : ℝ) : ‖complex.exp (-b * x^2)‖ = exp (-b.re * x^2) :=
by rw [complex.norm_eq_abs, complex.abs_exp, ←of_real_pow, mul_comm (-b) _, of_real_mul_re,
  neg_re, mul_comm]

lemma integrable_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) : integrable (λ x:ℝ, cexp (-b * x^2)) :=
begin
  refine ⟨(complex.continuous_exp.comp
    (continuous_const.mul (continuous_of_real.pow 2))).ae_strongly_measurable, _⟩,
  rw ←has_finite_integral_norm_iff,
  simp_rw norm_cexp_neg_mul_sq,
  exact (integrable_exp_neg_mul_sq hb).2,
end

lemma integrable_mul_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) :
  integrable (λ x:ℝ, ↑x * cexp (-b * x^2)) :=
begin
  refine ⟨(continuous_of_real.mul (complex.continuous_exp.comp _)).ae_strongly_measurable, _⟩,
  { exact continuous_const.mul (continuous_of_real.pow 2) },
  have := (integrable_mul_exp_neg_mul_sq hb).has_finite_integral,
  rw ←has_finite_integral_norm_iff at this ⊢,
  convert this,
  ext1 x,
  rw [norm_mul, norm_mul, norm_cexp_neg_mul_sq b, complex.norm_eq_abs, abs_of_real,
    real.norm_eq_abs, norm_of_nonneg (exp_pos _).le],
end

lemma integral_mul_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) :
  ∫ r:ℝ in Ioi 0, (r : ℂ) * cexp (-b * r ^ 2) = (2 * b)⁻¹ :=
begin
  have hb' : b ≠ 0 := by { contrapose! hb, rw [hb, zero_re], },
  refine tendsto_nhds_unique (interval_integral_tendsto_integral_Ioi _
    (integrable_mul_cexp_neg_mul_sq hb).integrable_on filter.tendsto_id) _,
  have A : ∀ x:ℂ, has_deriv_at (λ x, - (2 * b)⁻¹ * cexp (-b * x^2)) (x * cexp (- b * x^2)) x,
  { intro x,
    convert (((has_deriv_at_pow 2 x)).const_mul (-b)).cexp.const_mul (- (2 * b)⁻¹) using 1,
    field_simp [hb'],
    ring },
  have : ∀ (y : ℝ), ∫ x in 0..(id y), ↑x * cexp (-b * x^2)
      = (- (2 * b)⁻¹ * cexp (-b * y^2)) - (- (2 * b)⁻¹ * cexp (-b * 0^2)) :=
    λ y, interval_integral.integral_eq_sub_of_has_deriv_at
      (λ x hx, (A x).comp_of_real) (integrable_mul_cexp_neg_mul_sq hb).interval_integrable,
  simp_rw this,
  have L : tendsto (λ (x : ℝ), (2 * b)⁻¹ - (2 * b)⁻¹ * cexp (-b * x ^ 2)) at_top
    (𝓝 ((2 * b)⁻¹ - (2 * b)⁻¹ * 0)),
  { refine tendsto_const_nhds.sub (tendsto.const_mul _ $ tendsto_zero_iff_norm_tendsto_zero.mpr _),
    simp_rw norm_cexp_neg_mul_sq b,
    exact tendsto_exp_at_bot.comp
      (tendsto.neg_const_mul_at_top (neg_lt_zero.2 hb) (tendsto_pow_at_top two_ne_zero)) },
  simpa using L,
end

/-- The *square* of the Gaussian integral `∫ x:ℝ, exp (-b * x^2)` is equal to `π / b`. -/
lemma integral_gaussian_sq_complex {b : ℂ} (hb : 0 < b.re) :
  (∫ x:ℝ, cexp (-b * x^2)) ^ 2 = π / b :=
begin
  /- We compute `(∫ exp (-b x^2))^2` as an integral over `ℝ^2`, and then make a polar change
  of coordinates. We are left with `∫ r * exp (-b r^2)`, which has been computed in
  `integral_mul_cexp_neg_mul_sq` using the fact that this function has an obvious primitive. -/
  calc
  (∫ x:ℝ, cexp (-b * (x:ℂ)^2)) ^ 2
      = ∫ p : ℝ × ℝ, cexp (-b * ((p.1) : ℂ) ^ 2) * cexp (-b * ((p.2) : ℂ) ^ 2) :
    by { rw [pow_two, ← integral_prod_mul], refl }
  ... = ∫ p : ℝ × ℝ, cexp (- b * (p.1 ^ 2 + p.2 ^ 2)) :
    by { congr, ext1 p, rw [← complex.exp_add, mul_add], }
  ... = ∫ p in polar_coord.target, (p.1) • cexp (- b * ((p.1 * cos p.2) ^ 2 + (p.1 * sin p.2)^2)) :
    begin
      rw ← integral_comp_polar_coord_symm,
      simp only [polar_coord_symm_apply, of_real_mul, of_real_cos, of_real_sin],
    end
  ... = (∫ r in Ioi (0 : ℝ), r * cexp (-b * r^2)) * (∫ θ in Ioo (-π) π, 1) :
    begin
      rw ← set_integral_prod_mul,
      congr' with p : 1,
      rw mul_one,
      congr,
      conv_rhs { rw [← one_mul ((p.1 : ℂ)^2), ← sin_sq_add_cos_sq (p.2 : ℂ)], },
      ring_exp,
    end
  ... = ↑π / b :
    begin
      have : 0 ≤ π + π, by linarith [real.pi_pos],
      simp only [integral_const, measure.restrict_apply', measurable_set_Ioo, univ_inter,
        volume_Ioo, sub_neg_eq_add, ennreal.to_real_of_real, this],
      rw [←two_mul, real_smul, mul_one, of_real_mul, of_real_bit0, of_real_one,
        integral_mul_cexp_neg_mul_sq hb],
      field_simp [(by { contrapose! hb, rw [hb, zero_re] } : b ≠ 0)],
      ring,
    end
end

theorem integral_gaussian (b : ℝ) : ∫ x, exp (-b * x^2) = sqrt (π / b) :=
begin
  /- First we deal with the crazy case where `b ≤ 0`: then both sides vanish. -/
  rcases le_or_lt b 0 with hb|hb,
  { rw [integral_undef, sqrt_eq_zero_of_nonpos],
    { exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb },
    { simpa only [not_lt, integrable_exp_neg_mul_sq_iff] using hb } },
  /- Assume now `b > 0`. Then both sides are non-negative and their squares agree. -/
  refine (sq_eq_sq _ (sqrt_nonneg _)).1 _,
  { exact integral_nonneg (λ x, (exp_pos _).le) },
  rw [←of_real_inj, of_real_pow, ←integral_of_real, sq_sqrt (div_pos pi_pos hb).le, of_real_div],
  convert integral_gaussian_sq_complex (by rwa of_real_re : 0 < (b:ℂ).re),
  ext1 x,
  rw [of_real_exp, of_real_mul, of_real_pow, of_real_neg],
end

lemma continuous_at_gaussian_integral (b : ℂ) (hb : 0 < re b) :
  continuous_at (λ c:ℂ, ∫ x:ℝ, cexp (-c * x^2)) b :=
begin
  let f : ℂ → ℝ → ℂ := λ (c : ℂ) (x : ℝ), cexp (-c * x ^ 2),
  obtain ⟨d, hd, hd'⟩ := exists_between hb,
  have f_meas : ∀ (c:ℂ), ae_strongly_measurable (f c) volume := λ c, by
  { apply continuous.ae_strongly_measurable,
    exact complex.continuous_exp.comp (continuous_const.mul (continuous_of_real.pow 2)) },
  have f_int : integrable (f b) volume,
  { simp_rw [←integrable_norm_iff (f_meas b), norm_cexp_neg_mul_sq b],
    exact integrable_exp_neg_mul_sq hb, },
  have f_cts : ∀ (x : ℝ), continuous_at (λ c, f c x) b :=
    λ x, (complex.continuous_exp.comp (continuous_id'.neg.mul continuous_const)).continuous_at,
  have f_le_bd : ∀ᶠ (c : ℂ) in 𝓝 b, ∀ᵐ (x : ℝ), ‖f c x‖ ≤ exp (-d * x ^ 2),
  { refine eventually_of_mem ((continuous_re.is_open_preimage _ is_open_Ioi).mem_nhds hd') _,
    refine λ c hc, ae_of_all _ (λ x, _),
    rw [norm_cexp_neg_mul_sq, exp_le_exp],
    exact mul_le_mul_of_nonneg_right (neg_le_neg (le_of_lt hc)) (sq_nonneg _) },
  exact continuous_at_of_dominated (eventually_of_forall f_meas) f_le_bd
    (integrable_exp_neg_mul_sq hd) (ae_of_all _ f_cts),
end

theorem integral_gaussian_complex {b : ℂ} (hb : 0 < re b) :
  ∫ x:ℝ, cexp (-b * x^2) = (π / b) ^ (1 / 2 : ℂ) :=
begin
  have nv : ∀ {b : ℂ}, (0 < re b) → (b ≠ 0),
  { intros b hb, contrapose! hb, rw hb, simp },
  refine (convex_halfspace_re_gt 0).is_preconnected.eq_of_sq_eq
    _ _ (λ c hc, _) (λ c hc, _) (by simp : 0 < re (1 : ℂ)) _ hb,
  { -- integral is continuous
    exact continuous_at.continuous_on continuous_at_gaussian_integral, },
  { -- `(π / b) ^ (1 / 2 : ℂ)` is continuous
    refine continuous_at.continuous_on (λ b hb, (continuous_at_cpow_const (or.inl _)).comp
      (continuous_at_const.div continuous_at_id (nv hb))),
    rw [div_re, of_real_im, of_real_re, zero_mul, zero_div, add_zero],
    exact div_pos (mul_pos pi_pos hb) (norm_sq_pos.mpr (nv hb)), },
  { -- squares of both sides agree
    dsimp only [pi.pow_apply],
    rw [integral_gaussian_sq_complex hc, sq],
    conv_lhs { rw ←cpow_one (↑π / c)},
    rw ← cpow_add _ _ (div_ne_zero (of_real_ne_zero.mpr pi_ne_zero) (nv hc)),
    norm_num },
  { -- RHS doesn't vanish
    rw [ne.def, cpow_eq_zero_iff, not_and_distrib],
    exact or.inl (div_ne_zero (of_real_ne_zero.mpr pi_ne_zero) (nv hc)) },
  { -- equality at 1
    have : ∀ (x : ℝ), cexp (-1 * x ^ 2) = exp (-1 * x ^ 2),
    { intro x,
      simp only [of_real_exp, neg_mul, one_mul, of_real_neg, of_real_pow] },
    simp_rw [this, integral_of_real],
    conv_rhs {  congr, rw [←of_real_one, ←of_real_div], skip,
      rw [←of_real_one, ←of_real_bit0, ←of_real_div]  },
    rw [←of_real_cpow, of_real_inj],
    convert integral_gaussian (1 : ℝ),
    { rwa [sqrt_eq_rpow] },
    { rw [div_one], exact pi_pos.le } },
end

/- The Gaussian integral on the half-line, `∫ x in Ioi 0, exp (-b * x^2)`, for complex `b`. -/
lemma integral_gaussian_complex_Ioi {b : ℂ} (hb : 0 < re b) :
  ∫ x:ℝ in Ioi 0, cexp (-b * x^2) = (π / b) ^ (1 / 2 : ℂ) / 2 :=
begin
  have full_integral := integral_gaussian_complex hb,
  have : measurable_set (Ioi (0:ℝ)) := measurable_set_Ioi,
  rw [←integral_add_compl this (integrable_cexp_neg_mul_sq hb), compl_Ioi] at full_integral,
  suffices : ∫ x:ℝ in Iic 0, cexp (-b * x^2) = ∫ x:ℝ in Ioi 0, cexp (-b * x^2),
  { rw [this, ←mul_two] at full_integral,
    rwa eq_div_iff, exact two_ne_zero },
  have : ∀ (c : ℝ), ∫ x in 0 .. c, cexp (-b * x^2) = ∫ x in -c .. 0, cexp (-b * x^2),
  { intro c,
    have := @interval_integral.integral_comp_sub_left _ _ _ _ 0 c (λ x, cexp (-b * x^2)) 0,
    simpa [zero_sub, neg_sq, neg_zero] using this },
  have t1 := interval_integral_tendsto_integral_Ioi _
     ((integrable_cexp_neg_mul_sq hb).integrable_on) tendsto_id,
  have t2 : tendsto (λ c:ℝ, ∫ x:ℝ in 0..c,
    cexp (-b * x^2)) at_top (𝓝 ∫ x:ℝ in Iic 0, cexp (-b * x^2)),
  { simp_rw this,
    refine interval_integral_tendsto_integral_Iic _ _ tendsto_neg_at_top_at_bot,
    apply (integrable_cexp_neg_mul_sq hb).integrable_on },
  exact tendsto_nhds_unique t2 t1,
end

/- The Gaussian integral on the half-line, `∫ x in Ioi 0, exp (-b * x^2)`, for real `b`. -/
lemma integral_gaussian_Ioi (b : ℝ) : ∫ x in Ioi 0, exp (-b * x^2) = sqrt (π / b) / 2 :=
begin
  rcases le_or_lt b 0 with hb|hb,
  { rw [integral_undef, sqrt_eq_zero_of_nonpos, zero_div],
    exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb,
    rwa [←integrable_on, integrable_on_Ioi_exp_neg_mul_sq_iff, not_lt] },
  rw [←of_real_inj, ←integral_of_real],
  convert integral_gaussian_complex_Ioi (by rwa of_real_re : 0 < (b:ℂ).re),
  { ext1 x, simp, },
  { rw [sqrt_eq_rpow, ←of_real_div, of_real_div, of_real_cpow],
    norm_num,
    exact (div_pos pi_pos hb).le, }
end

namespace complex

/-- The special-value formula `Γ(1/2) = √π`, which is equivalent to the Gaussian integral. -/
lemma Gamma_one_half_eq : Gamma (1 / 2) = sqrt π :=
begin
  -- first reduce to real integrals
  have hh : (1 / 2 : ℂ) = ↑(1 / 2 : ℝ),
  { simp only [one_div, of_real_inv, of_real_bit0, of_real_one] },
  have hh2 : (1 / 2 : ℂ).re = 1 / 2,
  { convert of_real_re (1 / 2 : ℝ) },
  replace hh2 : 0 < (1 / 2 : ℂ).re := by { rw hh2, exact one_half_pos, },
  rw [Gamma_eq_integral hh2, hh, Gamma_integral_of_real, of_real_inj],
  -- now do change-of-variables
  rw ←integral_comp_rpow_Ioi_of_pos zero_lt_two,
  have : eq_on (λ x:ℝ, (2 * x^((2:ℝ) - 1)) • (real.exp (-x^(2:ℝ)) * (x^(2:ℝ)) ^ (1 / (2:ℝ) - 1)))
  (λ x:ℝ, 2 * real.exp ((-1) * x ^ (2:ℕ))) (Ioi 0),
  { intros x hx, dsimp only,
    have : (x^(2:ℝ)) ^ (1 / (2:ℝ) - 1) = x⁻¹,
    { rw ←rpow_mul (le_of_lt hx), norm_num,
      rw [rpow_neg (le_of_lt hx), rpow_one] },
    rw [smul_eq_mul, this],
    field_simp [(ne_of_lt hx).symm],
    norm_num, ring },
  rw [set_integral_congr measurable_set_Ioi this, integral_mul_left, integral_gaussian_Ioi],
  field_simp, ring,
end

end complex
