/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import measure_theory.function.continuous_map_dense
import measure_theory.integral.integral_eq_improper
import measure_theory.group.integration
import topology.continuous_function.zero_at_infty
import analysis.fourier.fourier_transform

/-!
# The Riemann-Lebesgue Lemma

In this file we prove the Riemann-Lebesgue lemma for functions on `ℝ`: for any `L¹` function `f`
(valued in some complete normed space `E`), the integral

`∫ (x : ℝ), exp (↑(t * x) * I) • f x`

tends to zero as `t → ∞`. We prove this first for continuous compactly-supported functions, then
deduce the general case from this and the density of continuous compactly-supported functions in
the `L¹` space.

## Main results

- `tendsto_integral_mul_exp_at_top`: the Riemann-Lebesgue lemma for `L¹` functions on `ℝ`.
- `real.fourier_integral_zero_at_infty`: reformulation in terms of Fourier integrals.
-/

open measure_theory filter complex set
open_locale filter topology real ennreal fourier_transform


section continuous_compact_support

variables {E : Type*} [normed_add_comm_group E] [normed_space ℂ E] {f : ℝ → E}

/-- The integrand in the Riemann-Lebesgue lemma is integrable. -/
lemma fourier_integrand_integrable (hf : integrable f) (t : ℝ) :
  integrable (λ x:ℝ, exp (↑(t * x) * I) • f x) :=
begin
  rw ←integrable_norm_iff,
  simp_rw [norm_smul, norm_exp_of_real_mul_I, one_mul],
  exacts [hf.norm, (continuous.ae_strongly_measurable (by continuity)).smul hf.1],
end

variable [complete_space E]

/-- Shifting `f` by `π / t` negates the integral in the Riemann-Lebesgue lemma. -/
lemma fourier_integral_half_period_translate {t : ℝ} (ht : t ≠ 0) :
  ∫ x:ℝ, exp (↑(t * x) * I) • f (x + π / t) = -∫ x:ℝ, exp (↑(t * x) * I) • f x :=
begin
  have : (λ x:ℝ, exp (↑(t * x) * I) • f (x + π / t)) =
    (λ x:ℝ, (λ y:ℝ, -exp (↑(t * y) * I) • f y) (x + π / t)),
  { ext1 x, dsimp only,
    rw [of_real_mul, of_real_mul, of_real_add, mul_add, add_mul, exp_add, ←neg_mul],
    replace ht := complex.of_real_ne_zero.mpr ht,
    have : ↑t * ↑(π / t) * I = π * I, by { field_simp, ring },
    rw [this, exp_pi_mul_I], ring_nf, },
  rw [this, integral_add_right_eq_self],
  simp_rw [neg_smul, integral_neg],
end

/-- Rewrite the Riemann-Lebesgue integral in a form that allows us to use uniform continuity. -/
lemma fourier_integral_eq_half_sub_half_period_translate
  {t : ℝ} (ht : t ≠ 0) (hf : integrable f) :
  ∫ x:ℝ, exp (↑(t * x) * I) • f x =
  (1 / (2 : ℂ)) • ∫ x:ℝ, exp (↑(t * x) * I) • (f x - f (x + π / t)) :=
begin
  simp_rw [smul_sub],
  rw [integral_sub, fourier_integral_half_period_translate ht, sub_eq_add_neg, neg_neg,
    ←two_smul ℂ _, ←@smul_assoc _ _ _ _ _ _ (is_scalar_tower.left ℂ), smul_eq_mul],
  norm_num,
  exacts [fourier_integrand_integrable hf t,
    fourier_integrand_integrable (hf.comp_add_right (π / t)) t],
end

/-- Riemann-Lebesgue Lemma for continuous and compactly-supported functions: the integral
`∫ x, exp (t * x * I) • f x` tends to 0 as `t` gets large.  -/
lemma tendsto_integral_mul_exp_at_top_of_continuous_compact_support
  (hf1 : continuous f) (hf2 : has_compact_support f) :
  tendsto (λ t:ℝ, ∫ x:ℝ, exp (↑(t * x) * I) • f x) at_top (𝓝 0) :=
begin
  simp_rw [normed_add_comm_group.tendsto_nhds_zero, eventually_at_top, ge_iff_le],
  intros ε hε,
  -- Extract an explicit candidate bound on `t` from uniform continuity.
  obtain ⟨R, hR1, hR2⟩ := hf2.exists_pos_le_norm,
  obtain ⟨δ, hδ1, hδ2⟩ := metric.uniform_continuous_iff.mp
    (hf2.uniform_continuous_of_continuous hf1) (ε / (1 + 2 * R)) (div_pos hε (by positivity)),
  refine ⟨max π (1 + π / δ), λ t ht, _⟩,
  have tpos : 0 < t := lt_of_lt_of_le real.pi_pos ((le_max_left _ _).trans ht),
  -- Rewrite integral in terms of `f x - f (x + π / t)`.
  rw fourier_integral_eq_half_sub_half_period_translate (lt_of_lt_of_le
    (lt_max_of_lt_left real.pi_pos) ht).ne' (hf1.integrable_of_has_compact_support hf2),
  rw [norm_smul, norm_eq_abs, ←complex.of_real_one, ←of_real_bit0, ←of_real_div,
    complex.abs_of_nonneg one_half_pos.le],
  have : ε = (1 / 2) * (2 * ε), by { field_simp, ring, },
  rw [this, mul_lt_mul_left (one_half_pos : (0:ℝ) < 1/2)],
  have : ‖∫ (x : ℝ), exp (↑(t * x) * I) • (f x - f (x + π / t))‖ ≤ ∫ (x : ℝ),
    ‖exp (↑(t * x) * I) • (f x - f (x + π / t))‖, from norm_integral_le_integral_norm _,
  refine lt_of_le_of_lt this _,
  simp_rw [norm_smul, norm_exp_of_real_mul_I, one_mul],
  -- Show integral can be taken over `[-(R + 1), R] ⊂ ℝ`.
  let A := Icc (-(R + 1)) R,
  have int_Icc : ∫ (x : ℝ), ‖f x - f (x + π / t)‖ = ∫ x in A, ‖f x - f (x + π / t)‖,
  { refine (set_integral_eq_integral_of_forall_compl_eq_zero (λ x hx, _)).symm,
    rw [mem_Icc, not_and_distrib, not_le, not_le, lt_neg] at hx,
    suffices : (f x = 0 ∧ f (x + π / t) = 0), by { rw [this.1, this.2, sub_zero, norm_zero], },
    have tp : 0 < t := real.pi_pos.trans_le ((le_max_left _ _).trans ht),
    refine ⟨hR2 x $ le_abs.mpr _, hR2 _ $ le_abs.mpr _⟩,
    { cases hx,
      { exact or.inr ((le_add_of_nonneg_right zero_le_one).trans hx.le) },
      { exact or.inl hx.le } },
    { cases hx,
      { refine or.inr _,
        rw [neg_add, ←sub_eq_add_neg, le_sub_iff_add_le],
        refine le_trans (add_le_add_left _ R) hx.le,
        exact (div_le_one tp).mpr ((le_max_left _ _).trans ht) },
      { exact or.inl (hx.trans $ lt_add_of_pos_right _ $ div_pos real.pi_pos tp).le } } },
  rw int_Icc,
  -- Bound integral using fact that ‖f x - f (x + π / t)‖ is small.
  have bdA : ∀ x : ℝ, (x ∈ A) → ‖ ‖f x - f (x + π / t) ‖ ‖ ≤ ε / (1 + 2 * R),
  { simp_rw norm_norm,
    refine (λ x _, le_of_lt _),
    simp_rw dist_eq_norm at hδ2,
    apply hδ2,
    rw [sub_add_cancel', real.norm_eq_abs, abs_neg, abs_of_pos (div_pos real.pi_pos tpos),
      div_lt_iff tpos, mul_comm, ←div_lt_iff hδ1],
    linarith [(le_max_right π (1 + π / δ)).trans ht] },
  have bdA2 := norm_set_integral_le_of_norm_le_const (measure_Icc_lt_top : volume A < ∞) bdA _,
  swap, { apply continuous.ae_strongly_measurable,
    exact (continuous_norm.comp $ continuous.sub hf1 $ continuous.comp hf1 $
    continuous_id'.add continuous_const) },
  have : ‖ _ ‖ = ∫ (x : ℝ) in A, ‖f x - f (x + π / t)‖ :=
    real.norm_of_nonneg (set_integral_nonneg measurable_set_Icc (λ x hx, norm_nonneg _)),
  rw this at bdA2,
  refine lt_of_le_of_lt bdA2 _,
  rw [real.volume_Icc, (by ring : R - (-(R + 1)) = 1 + 2 * R)],
  have hh : 0 < 1 + 2 * R, by positivity,
  rw [ennreal.to_real_of_real hh.le, div_mul_cancel _ hh.ne', two_mul],
  exact lt_add_of_pos_left _ hε,
end


end continuous_compact_support

section L1

variables {E : Type*} [normed_add_comm_group E] [normed_space ℂ E][complete_space E]

/- If `f` and `g` are close in `L¹` norm, then their Fourier transforms are close in sup norm. -/
lemma fourier_L1_cts {f g : ℝ → E} (hf : integrable f) (hg : integrable g) {ε : ℝ}
  (hfg : ∫ (x : ℝ), ‖f x - g x‖ ≤ ε) (t : ℝ) :
  ‖(∫ x:ℝ, exp (↑(t * x) * I) • f x) - (∫ x:ℝ, exp (↑(t * x) * I) • g x)‖ ≤ ε :=
begin
  rw ←integral_sub (fourier_integrand_integrable hf _) (fourier_integrand_integrable hg _),
  refine (norm_integral_le_integral_norm _).trans _,
  refine (integral_mono _ (hf.sub hg).norm _).trans hfg,
  { exact ((fourier_integrand_integrable hf _).sub (fourier_integrand_integrable hg _)).norm },
  intro x, convert le_refl _, dsimp,
  rw [←smul_sub, norm_smul, norm_eq_abs, abs_exp_of_real_mul_I, one_mul],
end

/-- Riemann-Lebesgue lemma for integrable functions. -/
theorem tendsto_integral_mul_exp_at_top {f : ℝ → E} (hfi : integrable f) :
  tendsto (λ t:ℝ, ∫ x:ℝ, exp (↑(t * x) * I) • f x) at_top (𝓝 0) :=
metric.tendsto_nhds.mpr $ λ ε hε, begin
  haveI : normal_space ℝ := normal_space_of_t3_second_countable ℝ,
  obtain ⟨g, hg3, hg1, -, hg2⟩ :=
    integrable.exists_has_compact_support_integral_sub_le hfi (by linarith : 0 < ε/2),
  refine ((metric.tendsto_nhds.mp (tendsto_integral_mul_exp_at_top_of_continuous_compact_support
    hg1 hg2)) _ (by linarith : 0 < ε/2)).mp (eventually_of_forall (λ t hI, _)),
  rw dist_eq_norm at hI ⊢,
  have := add_lt_add_of_le_of_lt
    (fourier_L1_cts hfi (hg1.integrable_of_has_compact_support hg2) hg3 t) hI,
  rw add_halves at this,
  refine ((le_of_eq _).trans (norm_add_le _ _)).trans_lt this,
  simp only [sub_zero, sub_add_cancel],
end

lemma tendsto_integral_mul_exp_at_bot {f : ℝ → E} (hfi : integrable f) :
  tendsto (λ t:ℝ, ∫ x:ℝ, exp (↑(t * x) * I) • f x) at_bot (𝓝 0) :=
begin
  have hg2 : integrable (f ∘ has_neg.neg), from hfi.comp_neg,
  convert (tendsto_integral_mul_exp_at_top hg2).comp tendsto_neg_at_bot_at_top,
  ext1 t,
  simp_rw [function.comp_app, neg_mul, ←mul_neg],
  rw ←integral_neg_eq_self,
end

lemma zero_at_infty_integral_mul_exp {f : ℝ → E} (hfi : integrable f) :
   tendsto (λ t:ℝ, ∫ x:ℝ, exp (↑(t * x) * I) • f x) (cocompact ℝ) (𝓝 0) :=
begin
  rw [real.cocompact_eq, tendsto_sup],
  exact ⟨tendsto_integral_mul_exp_at_bot hfi, tendsto_integral_mul_exp_at_top hfi⟩
end

/-- Riemann-Lebesgue lemma: for an `L¹` function on `ℝ`, the Fourier transform of `f` tends to 0
at infinity. -/
lemma real.fourier_integral_zero_at_infty {f : ℝ → E} (hfi : integrable f) :
  tendsto (𝓕 f) (cocompact ℝ) (𝓝 0) :=
begin
  refine ((zero_at_infty_integral_mul_exp hfi).comp
    (tendsto_cocompact_mul_left₀
    (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) real.pi_pos.ne'))).congr (λ w, _),
  rw [real.fourier_integral_eq_integral_exp_smul, function.comp_app],
  congr' 1 with x:1,
  ring_nf,
end

end L1
