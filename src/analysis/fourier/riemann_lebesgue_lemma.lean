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

In this file we prove a weak form of the Riemann-Lebesgue lemma, stating that for any
compactly-supported continuous function `f` on `ℝ` (valued in some complete normed space `E`), the
integral

`∫ (x : ℝ), exp (↑(t * x) * I) • f x`

tends to zero as `t → ∞`. (The actual lemma is that this holds for all `L¹` functions `f`, which
follows from the result proved here together with the fact that continuous, compactly-supported
functions are dense in `L¹(ℝ)`, which will be proved in a future iteration.)

## Main results

- `tendsto_integral_mul_exp_at_top_of_continuous_compact_support`: the Riemann-Lebesgue lemma for
  continuous compactly-supported functions on `ℝ`.
-/

open measure_theory filter complex set
open_locale filter topology real ennreal

variables {E : Type*} [normed_add_comm_group E] [normed_space ℂ E] {f : ℝ → E}

section continuous_compact_support


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

lemma tendsto_integral_mul_exp_at_bot_of_continuous_compact_support
  (hf1 : continuous f) (hf2 : has_compact_support f) :
  tendsto (λ t:ℝ, ∫ x:ℝ, exp (↑(t * x) * I) • f x) at_bot (𝓝 0) :=
begin
  have hg2 : has_compact_support (f ∘ has_neg.neg),
    by simpa only [neg_one_smul] using hf2.comp_smul (neg_ne_zero.mpr $ one_ne_zero' ℝ),
  convert (tendsto_integral_mul_exp_at_top_of_continuous_compact_support (hf1.comp continuous_neg)
    hg2).comp tendsto_neg_at_bot_at_top,
  ext1 t,
  simp_rw [function.comp_app, neg_mul, ←mul_neg],
  rw ←integral_neg_eq_self,
end

lemma zero_at_infty_integral_mul_exp_of_continuous_compact_support
  (hf1 : continuous f) (hf2 : has_compact_support f) :
  tendsto (λ t:ℝ, ∫ x:ℝ, exp (↑(t * x) * I) • f x) (cocompact ℝ) (𝓝 0) :=
begin
  rw [real.cocompact_eq, tendsto_sup],
  exact ⟨tendsto_integral_mul_exp_at_bot_of_continuous_compact_support hf1 hf2,
    tendsto_integral_mul_exp_at_top_of_continuous_compact_support hf1 hf2⟩
end

open_locale fourier_transform

/-- Riemann-Lebesgue lemma for continuous compactly-supported functions: the Fourier transform
tends to 0 at infinity. -/
lemma real.fourier_integral_zero_at_infty_of_continuous_compact_support
  (hc : continuous f) (hs : has_compact_support f) :
  tendsto (𝓕 f) (cocompact ℝ) (𝓝 0) :=
begin
  refine ((zero_at_infty_integral_mul_exp_of_continuous_compact_support hc hs).comp
    (tendsto_cocompact_mul_left₀
    (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) real.pi_pos.ne'))).congr (λ w, _),
  rw [real.fourier_integral_eq_integral_exp_smul, function.comp_app],
  congr' 1 with x:1,
  ring_nf,
end

end continuous_compact_support

section L1

variable [complete_space E]

/-- Any continuous integrable function is `L¹` approximated by compactly-supported continuous
functions. This lemma is private since it is a stepping stone towards the more general result
`cts_cpct_support_dense` proved below. -/
private lemma compact_support_dense_aux1
  {f : ℝ → E} (hfc : continuous f) (hfi : integrable f) {ε : ℝ} (hε : 0 < ε) :
  ∃ (g : ℝ → E), (has_compact_support g) ∧ (continuous g) ∧ (∫ (x : ℝ), ‖f x - g x‖ < ε) :=
begin
  have := interval_integral_tendsto_integral hfi.norm tendsto_neg_at_top_at_bot tendsto_id,
  rw metric.tendsto_nhds at this,
  obtain ⟨R, hR1, hR2⟩ := ((this ε hε).and (eventually_gt_at_top 0)).exists,
  rw dist_eq_norm at hR1,
  dsimp at hR1,
  rw [interval_integral.integral_of_le (neg_lt_self hR2).le,
    ←integral_indicator (measurable_set_Ioc : measurable_set (Ioc (-R) R)),
    ←integral_sub _ hfi.norm] at hR1,
  swap,
  { rw integrable_indicator_iff (measurable_set_Ioc : measurable_set (Ioc (-R) R)),
    exact hfi.norm.integrable_on },
  rw [abs_of_nonpos, ←integral_neg] at hR1,
  simp_rw neg_sub at hR1,
  swap, { apply integral_nonpos, intro x,
    dsimp, rw [←neg_nonneg, neg_sub],
    rw indicator,
    split_ifs, { simp, }, { simp }, },
  -- Now hR1 tells us that a compactly-supported, but possibly not continuous, function is L1-close
  -- to f. So we now extract a continuous approximation to that.
  have a1 : is_closed (Ici (R + 1) ∪ Iic (-(R+1))) := is_closed_Ici.union is_closed_Iic,
  have a2 : is_closed (Icc (-R) R) := is_closed_Icc,
  have a3 : disjoint  (Ici (R + 1) ∪ Iic (-(R+1))) (Icc (-R) R),
  { rw disjoint_iff_forall_ne,
    intros x hx y hy, rw mem_Icc at hy,
    cases hx, { rw mem_Ici at hx,linarith }, { rw mem_Iic at hx,linarith } },
  haveI : normal_space ℝ := normal_space_of_t3_second_countable ℝ,
  obtain ⟨t, ht1, ht2, ht3⟩ := exists_continuous_zero_one_of_closed a1 a2 a3,
  refine ⟨(λ x, t x • f x), _, (continuous_map.continuous t).smul hfc, _⟩,
  { apply has_compact_support.smul_right,
    rw ←exists_compact_iff_has_compact_support,
    refine ⟨Icc (-(R+1)) (R + 1), is_compact_Icc, (λ x hx, _)⟩,
    rw [mem_Icc, not_and_distrib, not_le, not_le] at hx,
    apply ht1,
    rw [mem_union, mem_Ici, mem_Iic],
    cases hx, { right, linarith, }, { left, linarith },  },
  refine lt_of_le_of_lt _ hR1,
  refine integral_mono_of_nonneg (ae_of_all _ (λ a, norm_nonneg _)) _ (ae_of_all _ _),
  { have : (λ (a : ℝ), ‖f a‖ - (Ioc (-R) R).indicator (λ (x : ℝ), ‖f x‖) a)
     = (Ioc (-R) R)ᶜ.indicator (λ (x : ℝ), ‖f x‖), by { rw indicator_compl, ext1 x, simp,  },
    rw [this, integrable_indicator_iff],
    exact ((integrable_norm_iff hfi.1).mpr hfi).integrable_on,
    exact measurable_set_Ioc.compl,},
  intro a,
  rw indicator, split_ifs,
  { suffices : t a = 1, { rw this, simp },
    apply ht2, exact mem_of_mem_of_subset h Ioc_subset_Icc_self, },
  { specialize ht3 a,
    have : f a - t a • f a = (1 - t a) • f a, by rw [sub_smul, one_smul],
    rw [this, norm_smul, sub_zero],
    apply mul_le_of_le_one_left (norm_nonneg _),
    rw real.norm_eq_abs, rw _root_.abs_of_nonneg,
    linarith [ht3.1], linarith [ht3.2] },
end

/-- Any integrable function is `L¹` approximated by continuous integrable functions.
This lemma is private, since it is a stepping stone towards the more general result
`cts_cpct_support_dense` proved below. -/
private lemma compact_support_dense_aux2 {f : ℝ → E} (hf : integrable f) {ε : ℝ} (hε : 0 < ε) :
  ∃ (g : ℝ → E), (integrable g) ∧ (continuous g) ∧ (∫ (x : ℝ), ‖f x - g x‖ < ε) :=
begin
  haveI : normal_space ℝ := normal_space_of_t3_second_countable ℝ,
  have := Lp.bounded_continuous_function_dense E ennreal.one_ne_top (volume : measure ℝ),
  let f_Lp := mem_ℒp.to_Lp f (mem_ℒp_one_iff_integrable.mpr hf),
  have f_closure : f_Lp ∈ (Lp.bounded_continuous_function E 1 volume).topological_closure,
  { rw this, tauto, },
  obtain ⟨b, hb1, hb2⟩ := metric.mem_closure_iff.mp f_closure ε hε,
  obtain ⟨b0, hb0⟩ := Lp.mem_bounded_continuous_function_iff.mp hb1,
  -- We should be done here, but b0 is not quite b, and f_Lp is not quite f.
  have b_ae_eq : b0 =ᵐ[volume] b,
  { have t2 := continuous_map.coe_fn_to_ae_eq_fun volume b0.1,
    rw hb0 at t2,
    refine ae_eq_trans (ae_eq_refl _) t2.symm },
  have f_ae_eq : f_Lp =ᵐ[volume] f := mem_ℒp.coe_fn_to_Lp _,
  have fb_ae_eq : ((f_Lp - b) : ↥(Lp E 1 volume)) =ᵐ[volume] (f - b0),
  { have := Lp.coe_fn_sub f_Lp b,
    refine eventually.mp ((this.and f_ae_eq).and b_ae_eq) (eventually_of_forall _),
    intros x hx,
    rw [hx.1.1, pi.sub_apply, pi.sub_apply, hx.1.2, ←hx.2] },
  refine ⟨b0, (integrable_congr b_ae_eq).mpr (L1.integrable_coe_fn b), b0.continuous, _⟩,
  { rw dist_eq_norm at hb2,
    rw L1.norm_eq_integral_norm at hb2,
    convert hb2 using 1,
    apply integral_congr_ae,
    refine eventually.mp fb_ae_eq (eventually_of_forall _),
    dsimp,
    intros x hx,
    rw hx }
end

/-- An integrable function on `ℝ` can be approximated arbitrarily closely in `L¹` norm by continuous
and compactly-supported functions. -/
lemma cts_cpct_support_dense {f : ℝ → E} (hf : integrable f) {ε : ℝ} (hε : 0 < ε) :
  ∃ (g : ℝ → E), (continuous g) ∧ (has_compact_support g) ∧ (∫ (x : ℝ), ‖f x - g x‖ < ε) :=
begin
  obtain ⟨j, hj1, hj2, hj3⟩ := compact_support_dense_aux2 hf (by linarith : 0 < ε / 2),
  obtain ⟨g, hg1, hg2, hg3⟩ := compact_support_dense_aux1 hj2 hj1 (by linarith : 0 < ε / 2),
  refine ⟨g, hg2, hg1, _⟩,
  rw (by ring : ε = ε/2 + ε/2),
  refine lt_of_le_of_lt _ (add_lt_add hj3 hg3),
  have hg4 : integrable g := hg2.integrable_of_has_compact_support hg1,
  rw ←integral_add,
  refine integral_mono_of_nonneg (eventually_of_forall (λ x, norm_nonneg _)) _ _,
  { exact integrable.add (hf.sub hj1).norm (hj1.sub hg4).norm, },
  { refine eventually_of_forall (λ x, _),
    convert le_trans (le_refl _) (norm_add_le _ _),
    rw [add_sub, sub_add_cancel], },
  exacts [(hf.sub hj1).norm, (hj1.sub hg4).norm],
end

/- If `f` and `g` are close in `L¹` norm, then their Fourier transforms are close in sup norm. -/
lemma fourier_L1_cts {f g : ℝ → E} (hf : integrable f) (hg : integrable g) {ε : ℝ}
  (hfg : ∫ (x : ℝ), ‖f x - g x‖ < ε) (t : ℝ) :
  ‖(∫ x:ℝ, exp (↑(t * x) * I) • f x) - (∫ x:ℝ, exp (↑(t * x) * I) • g x)‖ < ε :=
begin
  rw ←integral_sub (fourier_integrand_integrable hf _) (fourier_integrand_integrable hg _),
  refine lt_of_le_of_lt (norm_integral_le_integral_norm _) _,
  refine lt_of_le_of_lt (integral_mono _ (hf.sub hg).norm _) hfg,
  { exact ((fourier_integrand_integrable hf _).sub (fourier_integrand_integrable hg _)).norm },
  intro x, convert le_refl _, dsimp,
  rw [←smul_sub, norm_smul, norm_eq_abs, abs_exp_of_real_mul_I, one_mul],
end

/-- Riemann-Lebesgue lemma for integrable functions. -/
theorem tendsto_integral_mul_exp_at_top {f : ℝ → E} (hfi : integrable f) :
  tendsto (λ t:ℝ, ∫ x:ℝ, exp (↑(t * x) * I) • f x) at_top (𝓝 0) :=
metric.tendsto_nhds.mpr $ λ ε hε, begin
  obtain ⟨g, hg1, hg2, hg3⟩ := cts_cpct_support_dense hfi (by linarith : 0 < ε/2),
  refine ((metric.tendsto_nhds.mp (tendsto_integral_mul_exp_at_top_of_continuous_compact_support
    hg1 hg2)) _ (by linarith : 0 < ε/2)).mp (eventually_of_forall (λ t hI, _)),
  rw dist_eq_norm at hI ⊢,
  have := add_lt_add (fourier_L1_cts hfi (hg1.integrable_of_has_compact_support hg2) hg3 t) hI,
  rw (by ring : ε/2 + ε/2 = ε) at this,
  refine ((le_of_eq _).trans (norm_add_le _ _)).trans_lt this,
  simp only [sub_zero, sub_add_cancel],
end

end L1
