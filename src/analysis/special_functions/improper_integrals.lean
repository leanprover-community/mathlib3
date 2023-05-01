/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import measure_theory.integral.integral_eq_improper
import measure_theory.group.integration
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

open real set filter measure_theory interval_integral
open_locale topology

-- TODO: This should probably be moved elsewhere, but where?
lemma integral_comp_neg_Iic {E : Type*}
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E] (c : ℝ) (f : ℝ → E) :
  ∫ x in Iic c, f (-x) = ∫ x in Ioi (-c), f x :=
begin
  have A : measurable_embedding (λ x : ℝ, -x),
    from (homeomorph.neg ℝ).closed_embedding.measurable_embedding,
  have := A.set_integral_map f (Ici (-c)),
  rw measure.map_neg_eq_self (volume : measure ℝ) at this,
  simp_rw [←integral_Ici_eq_integral_Ioi, this, neg_preimage, preimage_neg_Ici, neg_neg],
end

lemma integral_comp_neg_Ioi {E : Type*}
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E] (c : ℝ) (f : ℝ → E) :
  ∫ x in Ioi c, f (-x) = ∫ x in Iic (-c), f x :=
begin
  rw [←neg_neg c, ←integral_comp_neg_Iic],
  simp only [neg_neg],
end

lemma integrable_on_exp_Iic (c : ℝ) : integrable_on exp (Iic c) :=
begin
  refine integrable_on_Iic_of_interval_integral_norm_bounded (exp c) c (λ y,
    interval_integrable_exp.1) tendsto_id (eventually_of_mem (Iic_mem_at_bot 0) (λ y hy, _)),
  simp_rw [(norm_of_nonneg (exp_pos _).le), integral_exp, sub_le_self_iff],
  exact (exp_pos _).le,
end

lemma integral_exp_Iic (c : ℝ) : ∫ (x : ℝ) in Iic c, exp x = exp c :=
begin
  refine tendsto_nhds_unique (interval_integral_tendsto_integral_Iic _ (integrable_on_exp_Iic _)
    tendsto_id) _,
  simp_rw [integral_exp, (show 𝓝 (exp c) = 𝓝 (exp c - 0), by rw sub_zero)],
  exact tendsto_exp_at_bot.const_sub _,
end

lemma integral_exp_Iic_zero : ∫ (x : ℝ) in Iic 0, exp x = 1 := exp_zero ▸ integral_exp_Iic 0

lemma integral_exp_neg_Ioi (c : ℝ) : ∫ (x : ℝ) in Ioi c, exp (-x) = exp (-c) :=
by simpa only [integral_comp_neg_Ioi] using integral_exp_Iic (-c)

lemma integral_exp_neg_Ioi_zero : ∫ (x : ℝ) in Ioi 0, exp (-x) = 1 :=
by simpa only [neg_zero, exp_zero] using integral_exp_neg_Ioi 0

/-- If `0 < c`, then `(λ t : ℝ, t ^ a)` is integrable on `(c, ∞)` for all `a < -1`. -/
lemma integrable_on_Ioi_rpow_of_lt {a : ℝ} (ha : a < -1) {c : ℝ} (hc : 0 < c) :
  integrable_on (λ t : ℝ, t ^ a) (Ioi c) :=
begin
  have hd : ∀ (x : ℝ) (hx : x ∈ Ici c), has_deriv_at (λ t, t ^ (a + 1) / (a + 1)) (x ^ a) x,
  { intros x hx,
    rw show x ^ a = ((a + 1) * x ^ a) / (a + 1), by { rw [mul_comm, mul_div_cancel], linarith },
    convert (has_deriv_at_rpow_const (or.inl (hc.trans_le hx).ne')).div_const _,
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
