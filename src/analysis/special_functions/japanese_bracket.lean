/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.special_functions.integrals
import analysis.special_functions.pow
import measure_theory.integral.layercake
import tactic.positivity

/-!
# Japanese Bracket

In this file, we show that Japanese bracket $(1 + \|x\|^2)^{1/2}$ can be estimated from above
and below by $1 + \|x\|$.
The functions $(1 + \|x\|^2)^{-r/2}$ and $(1 + |x|)^{-r}$ are integrable provided that `r` is larger
than the dimension.

## Main statements

* `integrable_one_add_norm`: the function $(1 + |x|)^{-r}$ is integrable
* `integrable_jap` the Japanese bracket is integrable

-/


noncomputable theory

open_locale big_operators nnreal filter topology ennreal

open asymptotics filter set real measure_theory finite_dimensional

variables {E : Type*} [normed_add_comm_group E]

lemma sqrt_one_add_norm_sq_le (x : E) : real.sqrt (1 + ‖x‖^2) ≤ 1 + ‖x‖ :=
begin
  refine le_of_pow_le_pow 2 (by positivity) two_pos _,
  simp [sq_sqrt (zero_lt_one_add_norm_sq x).le, add_pow_two],
end

lemma one_add_norm_le_sqrt_two_mul_sqrt (x : E) : 1 + ‖x‖ ≤ (real.sqrt 2) * sqrt (1 + ‖x‖^2) :=
begin
  suffices : (sqrt 2 * sqrt (1 + ‖x‖ ^ 2)) ^ 2 - (1 + ‖x‖) ^ 2 = (1 - ‖x‖) ^2,
  { refine le_of_pow_le_pow 2 (by positivity) (by norm_num) _,
    rw [←sub_nonneg, this],
    positivity, },
  rw [mul_pow, sq_sqrt (zero_lt_one_add_norm_sq x).le, add_pow_two, sub_pow_two],
  norm_num,
  ring,
end

lemma rpow_neg_one_add_norm_sq_le {r : ℝ} (x : E) (hr : 0 < r) :
  (1 + ‖x‖^2)^(-r/2) ≤ 2^(r/2) * (1 + ‖x‖)^(-r) :=
begin
  have h1 : 0 ≤ (2 : ℝ) := by positivity,
  have h3 : 0 < sqrt 2 := by positivity,
  have h4 : 0 < 1 + ‖x‖ := by positivity,
  have h5 : 0 < sqrt (1 + ‖x‖ ^ 2) := by positivity,
  have h6 : 0 < sqrt 2 * sqrt (1 + ‖x‖^2) := mul_pos h3 h5,
  rw [rpow_div_two_eq_sqrt _ h1, rpow_div_two_eq_sqrt _ (zero_lt_one_add_norm_sq x).le,
    ←inv_mul_le_iff (rpow_pos_of_pos h3 _), rpow_neg h4.le, rpow_neg (sqrt_nonneg _), ←mul_inv,
    ←mul_rpow h3.le h5.le, inv_le_inv (rpow_pos_of_pos h6 _) (rpow_pos_of_pos h4 _),
    rpow_le_rpow_iff h4.le h6.le hr],
  exact one_add_norm_le_sqrt_two_mul_sqrt _,
end

lemma le_rpow_one_add_norm_iff_norm_le {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : E) :
  t ≤ (1 + ‖x‖) ^ -r ↔ ‖x‖ ≤ t ^ -r⁻¹ - 1 :=
begin
  rw [le_sub_iff_add_le', neg_inv],
  exact (real.le_rpow_inv_iff_of_neg (by positivity) ht (neg_lt_zero.mpr hr)).symm,
end

variables (E)

lemma closed_ball_rpow_sub_one_eq_empty_aux {r t : ℝ} (hr : 0 < r) (ht : 1 < t) :
  metric.closed_ball (0 : E) (t^(-r⁻¹) - 1) = ∅ :=
begin
  rw [metric.closed_ball_eq_empty, sub_neg],
  exact real.rpow_lt_one_of_one_lt_of_neg ht (by simp only [hr, right.neg_neg_iff, inv_pos]),
end

variables [normed_space ℝ E] [finite_dimensional ℝ E]

variables {E}

lemma finite_integral_rpow_sub_one_pow_aux {r : ℝ} (n : ℕ) (hnr : (n : ℝ) < r) :
  ∫⁻ (x : ℝ) in Ioc 0 1, ennreal.of_real ((x ^ -r⁻¹ - 1) ^ n) < ∞ :=
begin
  have hr : 0 < r := lt_of_le_of_lt n.cast_nonneg hnr,
  have h_int : ∀ (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1),
    ennreal.of_real ((x ^ -r⁻¹ - 1) ^ n) ≤ ennreal.of_real (x ^ -(r⁻¹ * n)) :=
  begin
    intros x hx,
    have hxr : 0 ≤ x^ -r⁻¹ := rpow_nonneg_of_nonneg hx.1.le _,
    apply ennreal.of_real_le_of_real,
    rw [←neg_mul, rpow_mul hx.1.le, rpow_nat_cast],
    refine pow_le_pow_of_le_left _ (by simp only [sub_le_self_iff, zero_le_one]) n,
    rw [le_sub_iff_add_le', add_zero],
    refine real.one_le_rpow_of_pos_of_le_one_of_nonpos hx.1 hx.2 _,
    rw [right.neg_nonpos_iff, inv_nonneg],
    exact hr.le,
  end,
  refine lt_of_le_of_lt (set_lintegral_mono (by measurability) (by measurability) h_int) _,
  refine integrable_on.set_lintegral_lt_top _,
  rw ←interval_integrable_iff_integrable_Ioc_of_le zero_le_one,
  apply interval_integral.interval_integrable_rpow',
  rwa [neg_lt_neg_iff, inv_mul_lt_iff' hr, one_mul],
end

lemma finite_integral_one_add_norm [measure_space E] [borel_space E]
  [(@volume E _).is_add_haar_measure] {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
  ∫⁻ (x : E), ennreal.of_real ((1 + ‖x‖) ^ -r) < ∞ :=
begin
  have hr : 0 < r := lt_of_le_of_lt (finrank ℝ E).cast_nonneg hnr,

  -- We start by applying the layer cake formula
  have h_meas : measurable (λ (ω : E), (1 + ‖ω‖) ^ -r) := by measurability,
  have h_pos : ∀ x : E, 0 ≤ (1 + ‖x‖) ^ -r :=
  by { intros x, positivity },
  rw lintegral_eq_lintegral_meas_le volume h_pos h_meas,

  -- We use the first transformation of the integrant to show that we only have to integrate from
  -- 0 to 1 and from 1 to ∞
  have h_int : ∀ (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)),
    (volume {a : E | t ≤ (1 + ‖a‖) ^ -r} : ennreal) =
    volume (metric.closed_ball (0 : E) (t^(-r⁻¹) - 1)) :=
  begin
    intros t ht,
    congr' 1,
    ext x,
    simp only [mem_set_of_eq, mem_closed_ball_zero_iff],
    exact le_rpow_one_add_norm_iff_norm_le hr (mem_Ioi.mp ht) x,
  end,
  rw set_lintegral_congr_fun measurable_set_Ioi (ae_of_all volume $ h_int),
  have hIoi_eq : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 := (set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm,
  have hdisjoint : disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by simp [disjoint_iff],
  rw [hIoi_eq, lintegral_union measurable_set_Ioi hdisjoint, ennreal.add_lt_top],

  have h_int' : ∀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1),
    (volume (metric.closed_ball (0 : E) (t^(-r⁻¹) - 1)) : ennreal) =
    ennreal.of_real ((t^(-r⁻¹) - 1) ^ finite_dimensional.finrank ℝ E)
      * volume (metric.ball (0:E) 1) :=
  begin
    intros t ht,
    refine volume.add_haar_closed_ball (0 : E) _,
    rw [le_sub_iff_add_le', add_zero],
    exact real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2 (by simp [hr.le]),
  end,
  have h_meas' : measurable (λ (a : ℝ), ennreal.of_real ((a ^ -r⁻¹ - 1) ^ finrank ℝ E)) :=
  by measurability,
  split,
  -- The integral from 0 to 1:
  { rw [set_lintegral_congr_fun measurable_set_Ioc (ae_of_all volume $ h_int'),
      lintegral_mul_const _ h_meas', ennreal.mul_lt_top_iff],
    left,
    -- We calculate the integral
    exact ⟨finite_integral_rpow_sub_one_pow_aux (finrank ℝ E) hnr, measure_ball_lt_top⟩ },

  -- The integral from 1 to ∞ is zero:
  have h_int'' : ∀ (t : ℝ) (ht : t ∈ Ioi (1 : ℝ)),
    (volume (metric.closed_ball (0 : E) (t^(-r⁻¹) - 1)) : ennreal) = 0 :=
  λ t ht, by rw [closed_ball_rpow_sub_one_eq_empty_aux E hr ht, measure_empty],

  -- The integral over the constant zero function is finite:
  rw [set_lintegral_congr_fun measurable_set_Ioi (ae_of_all volume $ h_int''), lintegral_const 0,
    zero_mul],
  exact with_top.zero_lt_top,
end

lemma integrable_one_add_norm [measure_space E] [borel_space E] [(@volume E _).is_add_haar_measure]
  {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
  integrable (λ (x : E), (1 + ‖x‖) ^ -r) :=
begin
  refine ⟨by measurability, _⟩,
  -- Lower Lebesgue integral
  have : ∫⁻ (a : E), ‖(1 + ‖a‖) ^ -r‖₊ = ∫⁻ (a : E), ennreal.of_real ((1 + ‖a‖) ^ -r) :=
  lintegral_nnnorm_eq_of_nonneg (λ _, rpow_nonneg_of_nonneg (by positivity) _),
  rw [has_finite_integral, this],
  exact finite_integral_one_add_norm hnr,
end

lemma integrable_rpow_neg_one_add_norm_sq [measure_space E] [borel_space E]
  [(@volume E _).is_add_haar_measure] {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
  integrable (λ (x : E), (1 + ‖x‖^2) ^ (-r/2)) :=
begin
  have hr : 0 < r := lt_of_le_of_lt (finrank ℝ E).cast_nonneg hnr,
  refine ((integrable_one_add_norm hnr).const_mul $ 2 ^ (r / 2)).mono (by measurability)
    (eventually_of_forall $ λ x, _),
  have h1 : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-r/2) := by positivity,
  have h2 : 0 ≤ (1 + ‖x‖) ^ -r := by positivity,
  have h3 : 0 ≤ (2 : ℝ)^(r/2) := by positivity,
  simp_rw [norm_mul, norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg h3],
  exact rpow_neg_one_add_norm_sq_le _ hr,
end
