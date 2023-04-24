/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import measure_theory.integral.integral_eq_improper
import measure_theory.integral.exp_decay
import analysis.special_functions.integrals

/-!
# Evaluation of specific improper integrals

This file contains some integrability results, and evaluations of integrals, over `ℝ` or over
half-infinite intervals in `ℝ`.

## See also

- `analysis.special_functions.integrals` -- integrals over finite intervals
- `analysis.special_functions.gaussian` -- integral of `exp (-x ^ 2)`
-/

open real set filter measure_theory
open_locale topology

lemma integral_exp_neg_Ioi : ∫ (x : ℝ) in Ioi 0, exp (-x) = 1 :=
begin
  have h : ∀ (x : ℝ), x ∈ Ici (0:ℝ) → has_deriv_at (λ t, -exp (-t)) (exp (-x)) x,
  { intros x hx, simpa using ((has_deriv_at_exp _).comp _ (has_deriv_at_neg x)).neg},
  simpa only [neg_zero, zero_sub, neg_neg, exp_zero] using integral_Ioi_of_has_deriv_at_of_nonneg'
    h (λ x _, (exp_pos _).le) (tendsto_exp_neg_at_top_nhds_0).neg,
end

/-- If `0 < c`, then `(λ t : ℝ, t ^ a)` is integrable on `(c, ∞)` for all `a < -1`. -/
lemma integrable_on_Ioi_rpow_of_lt {a : ℝ} (ha : a < -1) {c : ℝ} (hc : 0 < c) :
  integrable_on (λ t : ℝ, t ^ a) (Ioi c) :=
begin
  have hd : ∀ (x : ℝ) (hx : x ∈ Ici c), has_deriv_at (λ t, t ^ (a + 1) / (a + 1)) (x ^ a) x,
  { intros x hx,
    simp_rw div_eq_inv_mul,
    have : x ^ a = (a + 1)⁻¹ * ((a + 1) * x ^ a),
    { rw [←mul_assoc, inv_mul_cancel, one_mul], linarith },
    rw this,
    convert (has_deriv_at_rpow_const (or.inl (hc.trans_le hx).ne')).const_mul _,
    abel },
  have ht : tendsto (λ t, t ^ (a + 1) / (a + 1)) at_top (𝓝 0),
  { rw ←zero_div,
    apply tendsto.div_const,
    simpa only [neg_neg] using tendsto_rpow_neg_at_top (by linarith : 0 < -(a + 1)) },
  exact integrable_on_Ioi_deriv_of_nonneg' hd (λ t ht, rpow_nonneg_of_nonneg (hc.trans ht).le a) ht
end

lemma integral_Ioi_rpow_of_lt {a : ℝ} (ha : a < -1) {c : ℝ} (hc : 0 < c) :
  ∫ (t : ℝ) in Ioi c, t ^ a = -c ^ (a + 1) / (a + 1) :=
begin
  refine tendsto_nhds_unique (interval_integral_tendsto_integral_Ioi c
    (integrable_on_Ioi_rpow_of_lt ha hc) tendsto_id) _,
  suffices : tendsto (λ (x : ℝ), (x ^ (a + 1) - c ^ (a + 1)) / (a + 1)) at_top
    (𝓝 $ -c ^ (a + 1) / (a + 1)),
  { refine this.congr' ((eventually_gt_at_top 0).mp (eventually_of_forall $ λ x hx, _)),
    rw [integral_rpow, id.def],
    exact or.inr ⟨ne_of_lt ha, not_mem_uIcc_of_lt hc hx⟩ },
  simp_rw [←zero_sub, sub_div],
  refine (tendsto.div_const _ _).sub_const _,
  simpa only [neg_neg] using tendsto_rpow_neg_at_top (by linarith : 0 < -(a + 1))
end

lemma integrable_on_Ioi_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
  integrable_on (λ t : ℝ, (t : ℂ) ^ a) (Ioi c) :=
begin
  rw [integrable_on, ←integrable_norm_iff, ←integrable_on],
  refine (integrable_on_Ioi_rpow_of_lt ha hc).congr_fun (λ x hx, _) measurable_set_Ioi,
  { dsimp only,
    rw [complex.norm_eq_abs, complex.abs_cpow_eq_rpow_re_of_pos (hc.trans hx)] },
  { refine continuous_on.ae_strongly_measurable (λ t ht, _) measurable_set_Ioi,
    exact (complex.continuous_at_of_real_cpow_const _ _
      (or.inr (hc.trans ht).ne')).continuous_within_at }
end

lemma integral_Ioi_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
  ∫ (t : ℝ) in Ioi c, (t : ℂ) ^ a = -(c : ℂ) ^ (a + 1) / (a + 1) :=
begin
  refine tendsto_nhds_unique (interval_integral_tendsto_integral_Ioi c
    (integrable_on_Ioi_cpow_of_lt ha hc) tendsto_id) _,
  suffices : tendsto (λ (x : ℝ), ((x : ℂ) ^ (a + 1) - (c : ℂ) ^ (a + 1)) / (a + 1)) at_top
    (𝓝 $ -c ^ (a + 1) / (a + 1)),
  { refine this.congr' ((eventually_gt_at_top 0).mp (eventually_of_forall $ λ x hx, _)),
    rw [integral_cpow, id.def],
    refine or.inr ⟨_, not_mem_uIcc_of_lt hc hx⟩,
    apply_fun complex.re,
    rw [complex.neg_re, complex.one_re],
    exact ha.ne },
  simp_rw [←zero_sub, sub_div],
  refine (tendsto.div_const _ _).sub_const _,
  rw tendsto_zero_iff_norm_tendsto_zero,
  refine (tendsto_rpow_neg_at_top (by linarith : 0 < -(a.re + 1))).congr'
    ((eventually_gt_at_top 0).mp (eventually_of_forall $ λ x hx, _)),
  simp_rw [neg_neg, complex.norm_eq_abs, complex.abs_cpow_eq_rpow_re_of_pos hx,
    complex.add_re, complex.one_re],
end
