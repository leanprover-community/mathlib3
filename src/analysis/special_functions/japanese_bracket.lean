/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.special_functions.integrals
import analysis.special_functions.pow
import measure_theory.integral.integral_eq_improper
import measure_theory.integral.layercake
import tactic.positivity

/-!
# Japanese Bracket

In this file, we show that Japanese bracket $(1 + \|x\|^2)^{1/2}$ can be estimated from above
and below by $1 + \|x\|$.
We prove that $(1 + \|x\|^2)^{-r/2}$ and $(1 + |x|)^{-r}$
are integrable for $r > n$.

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/


noncomputable theory

open_locale big_operators nnreal filter topological_space ennreal

open asymptotics filter set real measure_theory finite_dimensional

section

variables {α : Type*} [measurable_space α] [μ : measure α] {f g : α → ℝ≥0∞}
  {s : set α}

lemma lintegral_norm_eq_of_ae_nonneg {f : α → ℝ} {μ : measure α}
  (h_nonneg : 0 ≤ᵐ[μ] f) :
  ∫⁻ x, ennreal.of_real (∥f x∥) ∂μ = ∫⁻ x, ennreal.of_real (f x) ∂μ :=
begin
  apply lintegral_congr_ae,
  filter_upwards [h_nonneg] with x hx,
  rw norm_of_nonneg hx,
end

lemma lintegral_norm_eq_of_nonneg {f : α → ℝ} {μ : measure α}
  (h_nonneg : 0 ≤ f) :
  ∫⁻ x, ennreal.of_real (∥f x∥) ∂μ = ∫⁻ x, ennreal.of_real (f x) ∂μ :=
lintegral_norm_eq_of_ae_nonneg (filter.eventually_of_forall h_nonneg)

lemma integrable_on.lintegral_lt_top_ae' {f : α → ℝ} {s : set α} {μ : measure α}
  (hf : integrable_on f s μ) (h_nonneg : 0 ≤ᵐ[μ.restrict s] f) :
  ∫⁻ x in s, ennreal.of_real (f x) ∂μ < ⊤ :=
begin
  rw [←lintegral_norm_eq_of_ae_nonneg h_nonneg, ←has_finite_integral_iff_norm],
  exact hf.2,
end

lemma integrable_on.lintegral_lt_top_ae {f : α → ℝ} {s : set α} {μ : measure α}
  (hf : integrable_on f s μ) (hf' : ∀ᵐ x ∂μ, x ∈ s → 0 ≤ f x) :
  ∫⁻ x in s, ennreal.of_real (f x) ∂μ < ⊤ :=
begin
  let g := hf.1.mk _,
  have : ∫⁻ x in s, ennreal.of_real (f x) ∂μ = ∫⁻ x in s, ennreal.of_real (g x) ∂μ,
  { apply lintegral_congr_ae,
    filter_upwards [hf.1.ae_eq_mk] with x hx,
    rw hx },
  rw this,
  apply integrable_on.lintegral_lt_top_ae' (hf.congr hf.1.ae_eq_mk),
  apply (ae_restrict_iff (measurable_set_le measurable_zero (hf.1.measurable_mk))).2,
  filter_upwards [hf', ae_imp_of_ae_restrict hf.1.ae_eq_mk] with x hx h'x,
  assume xs,
  rw ← h'x xs,
  exact hx xs,
end

lemma integrable_on.lintegral_lt_top {f : ℝ → ℝ} {s : set ℝ} {μ : measure ℝ}
  (hf : integrable_on f s μ) (hf' : ∀ x : ℝ, x ∈ s → 0 ≤ f x) :
  ∫⁻ x in s, ennreal.of_real (f x) ∂μ < ⊤ :=
integrable_on.lintegral_lt_top_ae hf (ae_of_all μ hf')

end

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]

lemma rpow_two_sqrt {x : ℝ} (hx : 0 ≤ x): (real.sqrt x)^(2 : ℝ) = x :=
begin
  rw [sqrt_eq_rpow, ←rpow_mul hx],
  norm_num,
end

lemma pow_two_sqrt {x : ℝ} (hx : 0 ≤ x): (real.sqrt x)^2 = x :=
by rw [←rpow_two, rpow_two_sqrt hx]

lemma rpow_div_two_eq_sqrt {x : ℝ} (r : ℝ) (hx : 0 ≤ x) : x^(r/2) = x.sqrt^r :=
begin
  rw [sqrt_eq_rpow, ←rpow_mul hx],
  congr,
  ring,
end

lemma jap_le_one_add_norm (x : E) : real.sqrt (1 + ∥x∥^2) ≤ 1 + ∥x∥ :=
begin
  have h1 : 0 ≤ real.sqrt (1 + ∥x∥^2) := by positivity,
  have h1' : 0 ≤ 1 + ∥x∥^2 := by positivity,
  have h2 : 0 ≤ 1 + ∥x∥ := by positivity,
  have h3 : 0 < (2 : ℝ) := by positivity,
  rw ←rpow_le_rpow_iff h1 h2 h3,
  rw rpow_two_sqrt h1',
  rw rpow_two,
  rw add_pow_two,
  simp,
end

lemma one_add_norm_le_jap (x : E) : 1 + ∥x∥ ≤ (real.sqrt 2) * sqrt (1 + ∥x∥^2) :=
begin
  have h1 : 0 ≤ 1 + ∥x∥^2 := by positivity,
  have h2 : 0 ≤ (real.sqrt 2) * real.sqrt (1 + ∥x∥^2) := by positivity,
  have : (sqrt 2 * sqrt (1 + ∥x∥ ^ 2)) ^ 2 - (1 + ∥x∥) ^ 2 = (1 - ∥x∥) ^2 :=
  begin
    rw [mul_pow, pow_two_sqrt h1, add_pow_two, sub_pow_two],
    norm_num,
    ring,
  end,
  refine le_of_pow_le_pow 2 h2 (by norm_num) _,
  rw ←sub_nonneg,
  rw this,
  positivity,
end

lemma rpow_neg_jap_le_one_add_norm {r : ℝ} (x : E) (hr : 0 < r) :
  (1 + ∥x∥^2)^(-r/2) ≤ 2^(r/2) * (1 + ∥x∥)^(-r) :=
begin
  have h1 : 0 ≤ (2 : ℝ) := by positivity,
  have h2 : 0 ≤ (1 + ∥x∥^2) := by positivity,
  have h3 : 0 < sqrt 2 := by positivity,
  have h4 : 0 < 1 + ∥x∥ := by positivity,
  have h5 : 0 < sqrt (1 + ∥x∥ ^ 2) := by positivity,
  have h6 : 0 < sqrt 2 * sqrt (1 + ∥x∥^2) := mul_pos h3 h5,
  rw rpow_div_two_eq_sqrt _ h1,
  rw rpow_div_two_eq_sqrt _ h2,
  rw ←inv_mul_le_iff (rpow_pos_of_pos h3 _),
  rw [rpow_neg h4.le, rpow_neg (sqrt_nonneg _)],
  rw ←mul_inv,
  rw ←mul_rpow h3.le h5.le,
  rw inv_le_inv (rpow_pos_of_pos h6 _) (rpow_pos_of_pos h4 _),
  rw rpow_le_rpow_iff h4.le h6.le hr,
  exact one_add_norm_le_jap _,
end

variables [finite_dimensional ℝ E]

lemma continuous_foo {ε : ℝ} (hε : 0 < ε) :
  continuous (λ (x : E), (1 + ∥x∥)^(-((finrank ℝ E : ℝ) + ε))) :=
begin
  refine continuous.rpow_const (by continuity) _,
  intro,
  left,
  refine ne_of_gt _,
  positivity,
end

variables (E)

lemma le_neg_rpow_iff {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a ≤ b^(-c) ↔ b ≤ a^(-c⁻¹) :=
begin
  have hc' : 0 < c⁻¹ := by positivity,
  have hac : 0 < a^(c⁻¹) := rpow_pos_of_pos ha _,
  have hbc : 0 < b^(-c) := rpow_pos_of_pos hb _,
  rw [←rpow_le_rpow_iff ha.le hbc.le hc', ←rpow_mul hb.le],
  simp only [ne_of_gt hc, rpow_neg_one, neg_mul, mul_inv_cancel, ne.def, not_false_iff],
  rw [le_inv hac hb, ←rpow_neg_one, ←rpow_mul ha.le],
  simp,
end

lemma lt_neg_rpow_iff {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a < b^(-c) ↔ b < a^(-c⁻¹) :=
begin
  have hc' : 0 < c⁻¹ := by positivity,
  have hac : 0 < a^(c⁻¹) := rpow_pos_of_pos ha _,
  have hbc : 0 < b^(-c) := rpow_pos_of_pos hb _,
  rw [←rpow_lt_rpow_iff ha.le hbc.le hc', ←rpow_mul hb.le],
  simp only [ne_of_gt hc, rpow_neg_one, neg_mul, mul_inv_cancel, ne.def, not_false_iff],
  rw [lt_inv hac hb, ←rpow_neg_one, ←rpow_mul ha.le],
  simp,
end

lemma neg_rpow_lt_iff {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a^(-c) < b ↔ b^(-c⁻¹) < a :=
begin
  convert lt_neg_rpow_iff (rpow_pos_of_pos ha _) (rpow_pos_of_pos hb _) hc;
  simp [←rpow_mul ha.le, ←rpow_mul hb.le, ne_of_gt hc],
end

lemma neg_rpow_le_iff {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a^(-c) ≤ b ↔ b^(-c⁻¹) ≤ a :=
begin
  convert le_neg_rpow_iff (rpow_pos_of_pos ha _) (rpow_pos_of_pos hb _) hc;
  simp [←rpow_mul ha.le, ←rpow_mul hb.le, ne_of_gt hc],
end

lemma set_as_closed_ball {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
  {a : E | t ≤ (1 + ∥a∥) ^ -r} = metric.closed_ball 0 (t^(-r⁻¹) - 1) :=
begin
  ext,
  simp only [norm_eq_abs, mem_set_of_eq, mem_closed_ball_zero_iff],
  rw le_sub_iff_add_le',
  exact le_neg_rpow_iff ht (by positivity) hr,
end

lemma closed_ball_empty {r t : ℝ} (hr : 0 < r) (ht : 1 < t) :
  metric.closed_ball (0 : E) (t^(-r⁻¹) - 1) = ∅ :=
begin
  rw [metric.closed_ball_eq_empty, sub_neg,
    ←neg_rpow_lt_iff zero_lt_one (zero_lt_one.trans ht) hr],
  simp [ht],
end

variables {E}

lemma finite_foo' {r : ℝ} (n : ℕ) (hnr : (n : ℝ) < r) :
  ∫⁻ (x : ℝ) in Ioc 0 1, ennreal.of_real ((x ^ -r⁻¹ - 1) ^ n) < ⊤ :=
begin
  have hr : 0 < r := lt_of_le_of_lt n.cast_nonneg hnr,
  have h_int : ∀ (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1),
    ennreal.of_real ((x ^ -r⁻¹ - 1) ^ n) ≤ ennreal.of_real ((x ^ -r⁻¹) ^ n) :=
  begin
    intros x hx,
    have hxr : 0 ≤ x^ -r⁻¹ := rpow_nonneg_of_nonneg hx.1.le _,
    apply ennreal.of_real_le_of_real,
    refine pow_le_pow_of_le_left _ _ n,
    { rw [le_sub_iff_add_le', add_zero],
      rw ← le_neg_rpow_iff hx.1 zero_lt_one hr,
      simp [hx.2] },
    simp,
  end,
  refine lt_of_le_of_lt (set_lintegral_mono _ _ h_int) _,
  measurability, -- all involved functions are measurable
  have h_int' : ∀ (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1),
    ennreal.of_real ((x ^ -r⁻¹) ^ n) = ennreal.of_real (x ^ -(r⁻¹ * n)) :=
  begin
    intros x hx,
    congr' 1,
    rw [←rpow_nat_cast, ←rpow_mul hx.1.le, neg_mul],
  end,
  rw set_lintegral_congr_fun measurable_set_Ioc (ae_of_all volume h_int'),
  refine integrable_on.lintegral_lt_top _ _,
  { rw ←interval_integrable_iff_integrable_Ioc_of_le zero_le_one,
    apply interval_integral.interval_integrable_rpow',
    simp only [neg_lt_neg_iff],
    rw inv_mul_lt_iff' hr,
    simp [hnr], },
  intros x hx,
  exact rpow_nonneg_of_nonneg hx.1.le _,
end

lemma finite_foo [measure_space E] [borel_space E] [(@volume E _).is_add_haar_measure]
  {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
  ∫⁻ (x : E), ennreal.of_real ((1 + ∥x∥) ^ -r) < ⊤ :=
begin
  have hr : 0 < r := lt_of_le_of_lt (finrank ℝ E).cast_nonneg hnr,
  have h_int : ∀ (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)),
    (volume {a : E | t ≤ (1 + ∥a∥) ^ -r} : ennreal) =
    volume (metric.closed_ball (0 : E) (t^(-r⁻¹) - 1)) :=
  begin
    intros t ht,
    congr' 1,
    exact set_as_closed_ball E hr (mem_Ioi.mp ht),
  end,
  have h_int' : ∀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1),
    (volume (metric.closed_ball (0 : E) (t^(-r⁻¹) - 1)) : ennreal) =
    ennreal.of_real ((t^(-r⁻¹) - 1) ^ finite_dimensional.finrank ℝ E)
      * volume (metric.ball (0:E) 1) :=
  begin
    intros t ht,
    rw measure.add_haar_closed_ball,
    rw [le_sub_iff_add_le', add_zero, ← le_neg_rpow_iff ht.1 zero_lt_one hr],
    simp [ht.2],
  end,
  have h_int'' : ∀ (t : ℝ) (ht : t ∈ Ioi (1 : ℝ)),
    (volume (metric.closed_ball (0 : E) (t^(-r⁻¹) - 1)) : ennreal) = 0 :=
  begin
    intros t ht,
    rw closed_ball_empty E hr ht,
    simp,
  end,
  rw lintegral_eq_lintegral_meas_le,
  { -- We use the first transformation of the integrant to show that we only have to integrate from
    -- 0 to 1 and from 1 to ∞
    have hIoi_eq : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 :=
      (set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm,
    have hdisjoint : disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by simp [disjoint_iff],
    rw set_lintegral_congr_fun measurable_set_Ioi (ae_of_all volume $ h_int),
    rw [hIoi_eq, lintegral_union measurable_set_Ioi hdisjoint, ennreal.add_lt_top],
    split,
    -- The integral from 0 to 1:
    { rw set_lintegral_congr_fun measurable_set_Ioc (ae_of_all volume $ h_int'),
      rw lintegral_mul_const,
      { rw ennreal.mul_lt_top_iff,
        left,
        -- We calculate the integral
        use finite_foo' _ hnr,
        -- The unit ball has finite measure
        rw ←measure.add_haar_closed_unit_ball_eq_add_haar_unit_ball,
        exact (is_compact_closed_ball _ _).measure_lt_top, },
      measurability, },
    -- The integral from 1 to ∞ is zero:
    rw set_lintegral_congr_fun measurable_set_Ioi (ae_of_all volume $ h_int''),
    simp, },
  { intros x,
    simp only [pi.zero_apply, norm_eq_abs, neg_add_rev],
    refine rpow_nonneg_of_nonneg _ _,
    positivity, },
  measurability,
end

lemma foo [measure_space E] [borel_space E] [(@volume E _).is_add_haar_measure]
  {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
  integrable (λ (x : E), (1 + ∥x∥) ^ -r) :=
begin
  refine ⟨by measurability, _⟩,
  -- Lower Lebesgue integral
  have : ∫⁻ (a : E), ennreal.of_real (∥(1 + ∥a∥) ^ -r∥) =
    ∫⁻ (a : E), ennreal.of_real ((1 + ∥a∥) ^ -r) :=
  begin
    refine lintegral_norm_eq_of_nonneg (λ x, _),
    have h : 0 ≤ (1 + ∥x∥) ^ -r := rpow_nonneg_of_nonneg (by positivity) _,
    simp [h],
  end,
  rw [has_finite_integral_iff_norm, this],
  exact finite_foo hnr,
end

lemma integrable_jap [measure_space E] [borel_space E] [(@volume E _).is_add_haar_measure]
  {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
  integrable (λ (x : E), (1 + ∥x∥^2) ^ (-r/2)) :=
begin
  have hr : 0 < r := lt_of_le_of_lt (nat.cast_nonneg _) hnr,
  refine ((foo hnr).const_mul (2^(r/2))).mono (by measurability) (eventually_of_forall _),
  intros x,
  have h1 : 0 ≤ (1 + ∥x∥ ^ 2) ^ (-r/2) := rpow_nonneg_of_nonneg (by positivity) _,
  have h2 : 0 ≤ (1 + ∥x∥) ^ -r := rpow_nonneg_of_nonneg (by positivity) _,
  have h3 : 0 ≤ (2 : ℝ)^(r/2) := rpow_nonneg_of_nonneg (by positivity) _,
  simp_rw [norm_mul, norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg h3],
  exact rpow_neg_jap_le_one_add_norm _ hr,
end
