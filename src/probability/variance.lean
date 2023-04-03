/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Kexing Ying
-/
import probability.notation
import probability.integration

/-!
# Variance of random variables

We define the variance of a real-valued random variable as `Var[X] = 𝔼[(X - 𝔼[X])^2]` (in the
`probability_theory` locale).

## Main definitions

* `probability_theory.evariance`: the variance of a real-valued random variable as a extended
  non-negative real.
* `probability_theory.variance`: the variance of a real-valued random variable as a real number.

## Main results

* `probability_theory.variance_le_expectation_sq`: the inequality `Var[X] ≤ 𝔼[X^2]`.
* `probability_theory.meas_ge_le_variance_div_sq`: Chebyshev's inequality, i.e.,
      `ℙ {ω | c ≤ |X ω - 𝔼[X]|} ≤ ennreal.of_real (Var[X] / c ^ 2)`.
* `probability_theory.meas_ge_le_evariance_div_sq`: Chebyshev's inequality formulated with
  `evariance` without requiring the random variables to be L².
* `probability_theory.indep_fun.variance_add`: the variance of the sum of two independent
  random variables is the sum of the variances.
* `probability_theory.indep_fun.variance_sum`: the variance of a finite sum of pairwise
  independent random variables is the sum of the variances.
-/

open measure_theory filter finset

noncomputable theory

open_locale big_operators measure_theory probability_theory ennreal nnreal

namespace probability_theory

/-- The `ℝ≥0∞`-valued variance of a real-valued random variable defined as the Lebesgue integral of
`(X - 𝔼[X])^2`. -/
def evariance {Ω : Type*} {m : measurable_space Ω} (X : Ω → ℝ) (μ : measure Ω) : ℝ≥0∞ :=
∫⁻ ω, ‖X ω - μ[X]‖₊^2 ∂μ

/-- The `ℝ`-valued variance of a real-valued random variable defined by applying `ennreal.to_real`
to `evariance`. -/
def variance {Ω : Type*} {m : measurable_space Ω} (X : Ω → ℝ) (μ : measure Ω) : ℝ :=
(evariance X μ).to_real

variables {Ω : Type*} {m : measurable_space Ω} {X : Ω → ℝ} {μ : measure Ω}

lemma _root_.measure_theory.mem_ℒp.evariance_lt_top [is_finite_measure μ] (hX : mem_ℒp X 2 μ) :
  evariance X μ < ∞ :=
begin
  have := ennreal.pow_lt_top (hX.sub $ mem_ℒp_const $ μ[X]).2 2,
  rw [snorm_eq_lintegral_rpow_nnnorm two_ne_zero ennreal.two_ne_top,
    ← ennreal.rpow_two] at this,
  simp only [pi.sub_apply, ennreal.to_real_bit0, ennreal.one_to_real, one_div] at this,
  rw [← ennreal.rpow_mul, inv_mul_cancel (two_ne_zero : (2 : ℝ) ≠ 0), ennreal.rpow_one] at this,
  simp_rw ennreal.rpow_two at this,
  exact this,
end

lemma evariance_eq_top [is_finite_measure μ]
  (hXm : ae_strongly_measurable X μ) (hX : ¬ mem_ℒp X 2 μ) :
  evariance X μ = ∞ :=
begin
  by_contra h,
  rw [← ne.def, ← lt_top_iff_ne_top] at h,
  have : mem_ℒp (λ ω, X ω - μ[X]) 2 μ,
  { refine ⟨hXm.sub ae_strongly_measurable_const, _⟩,
    rw snorm_eq_lintegral_rpow_nnnorm two_ne_zero ennreal.two_ne_top,
    simp only [ennreal.to_real_bit0, ennreal.one_to_real, ennreal.rpow_two, ne.def],
    exact ennreal.rpow_lt_top_of_nonneg (by simp) h.ne },
  refine hX _,
  convert this.add (mem_ℒp_const $ μ[X]),
  ext ω,
  rw [pi.add_apply, sub_add_cancel],
end

lemma evariance_lt_top_iff_mem_ℒp [is_finite_measure μ]
  (hX : ae_strongly_measurable X μ) :
  evariance X μ < ∞ ↔ mem_ℒp X 2 μ :=
begin
  refine ⟨_, measure_theory.mem_ℒp.evariance_lt_top⟩,
  contrapose,
  rw [not_lt, top_le_iff],
  exact evariance_eq_top hX
end

lemma _root_.measure_theory.mem_ℒp.of_real_variance_eq [is_finite_measure μ]
  (hX : mem_ℒp X 2 μ) :
  ennreal.of_real (variance X μ) = evariance X μ :=
by { rw [variance, ennreal.of_real_to_real], exact hX.evariance_lt_top.ne, }

include m

lemma evariance_eq_lintegral_of_real (X : Ω → ℝ) (μ : measure Ω) :
  evariance X μ = ∫⁻ ω, ennreal.of_real ((X ω - μ[X])^2) ∂μ :=
begin
  rw evariance,
  congr,
  ext1 ω,
  rw [pow_two, ← ennreal.coe_mul, ← nnnorm_mul, ← pow_two],
  congr,
  exact (real.to_nnreal_eq_nnnorm_of_nonneg $ sq_nonneg _).symm,
end

lemma _root_.measure_theory.mem_ℒp.variance_eq_of_integral_eq_zero
  (hX : mem_ℒp X 2 μ) (hXint : μ[X] = 0) :
  variance X μ = μ[X^2] :=
begin
  rw [variance, evariance_eq_lintegral_of_real, ← of_real_integral_eq_lintegral_of_real,
    ennreal.to_real_of_real];
  simp_rw [hXint, sub_zero],
  { refl },
  { exact integral_nonneg (λ ω, pow_two_nonneg _) },
  { convert hX.integrable_norm_rpow two_ne_zero ennreal.two_ne_top,
    ext ω,
    simp only [pi.sub_apply, real.norm_eq_abs, ennreal.to_real_bit0, ennreal.one_to_real,
      real.rpow_two, pow_bit0_abs] },
  { exact ae_of_all _ (λ ω, pow_two_nonneg _) }
end

lemma _root_.measure_theory.mem_ℒp.variance_eq [is_finite_measure μ]
  (hX : mem_ℒp X 2 μ) :
  variance X μ = μ[(X - (λ ω, μ[X]))^2] :=
begin
  rw [variance, evariance_eq_lintegral_of_real, ← of_real_integral_eq_lintegral_of_real,
    ennreal.to_real_of_real],
  { refl },
  { exact integral_nonneg (λ ω, pow_two_nonneg _) },
  { convert (hX.sub $ mem_ℒp_const (μ[X])).integrable_norm_rpow
      two_ne_zero ennreal.two_ne_top,
    ext ω,
    simp only [pi.sub_apply, real.norm_eq_abs, ennreal.to_real_bit0, ennreal.one_to_real,
      real.rpow_two, pow_bit0_abs] },
  { exact ae_of_all _ (λ ω, pow_two_nonneg _) }
end

@[simp] lemma evariance_zero : evariance 0 μ = 0 :=
by simp [evariance]

lemma evariance_eq_zero_iff (hX : ae_measurable X μ) :
  evariance X μ = 0 ↔ X =ᵐ[μ] λ ω, μ[X] :=
begin
  rw [evariance, lintegral_eq_zero_iff'],
  split; intro hX; filter_upwards [hX] with ω hω,
  { simp only [pi.zero_apply, pow_eq_zero_iff, nat.succ_pos', ennreal.coe_eq_zero,
      nnnorm_eq_zero, sub_eq_zero] at hω,
    exact hω },
  { rw hω,
    simp },
  { measurability }
end

lemma evariance_mul (c : ℝ) (X : Ω → ℝ) (μ : measure Ω) :
  evariance (λ ω, c * X ω) μ = ennreal.of_real (c^2) * evariance X μ :=
begin
  rw [evariance, evariance, ← lintegral_const_mul' _ _ ennreal.of_real_lt_top.ne],
  congr,
  ext1 ω,
  rw [ennreal.of_real, ← ennreal.coe_pow, ← ennreal.coe_pow, ← ennreal.coe_mul],
  congr,
  rw [← sq_abs, ← real.rpow_two, real.to_nnreal_rpow_of_nonneg (abs_nonneg _), nnreal.rpow_two,
    ← mul_pow, real.to_nnreal_mul_nnnorm _ (abs_nonneg _)],
  conv_rhs { rw [← nnnorm_norm, norm_mul, norm_abs_eq_norm, ← norm_mul, nnnorm_norm, mul_sub] },
  congr,
  rw mul_comm,
  simp_rw [← smul_eq_mul, ← integral_smul_const, smul_eq_mul, mul_comm],
end

localized "notation (name := probability_theory.evariance) `eVar[` X `]` :=
  probability_theory.evariance X measure_theory.measure_space.volume" in probability_theory

@[simp] lemma variance_zero (μ : measure Ω) : variance 0 μ = 0 :=
by simp only [variance, evariance_zero, ennreal.zero_to_real]

lemma variance_nonneg (X : Ω → ℝ) (μ : measure Ω) :
  0 ≤ variance X μ :=
ennreal.to_real_nonneg

lemma variance_mul (c : ℝ) (X : Ω → ℝ) (μ : measure Ω) :
  variance (λ ω, c * X ω) μ = c^2 * variance X μ :=
begin
  rw [variance, evariance_mul, ennreal.to_real_mul, ennreal.to_real_of_real (sq_nonneg _)],
  refl,
end

lemma variance_smul (c : ℝ) (X : Ω → ℝ) (μ : measure Ω) :
  variance (c • X) μ = c^2 * variance X μ :=
variance_mul c X μ

lemma variance_smul' {A : Type*} [comm_semiring A] [algebra A ℝ]
  (c : A) (X : Ω → ℝ) (μ : measure Ω) :
  variance (c • X) μ = c^2 • variance X μ :=
begin
  convert variance_smul (algebra_map A ℝ c) X μ,
  { ext1 x, simp only [algebra_map_smul], },
  { simp only [algebra.smul_def, map_pow], }
end

localized "notation (name := probability_theory.variance) `Var[` X `]` :=
  probability_theory.variance X measure_theory.measure_space.volume" in probability_theory

omit m

variables [measure_space Ω]

lemma variance_def' [is_probability_measure (ℙ : measure Ω)]
  {X : Ω → ℝ} (hX : mem_ℒp X 2) :
  Var[X] = 𝔼[X^2] - 𝔼[X]^2 :=
begin
  rw [hX.variance_eq, sub_sq', integral_sub', integral_add'], rotate,
  { exact hX.integrable_sq },
  { convert integrable_const (𝔼[X] ^ 2),
    apply_instance },
  { apply hX.integrable_sq.add,
    convert integrable_const (𝔼[X] ^ 2),
    apply_instance },
  { exact ((hX.integrable one_le_two).const_mul 2).mul_const' _ },
  simp only [integral_mul_right, pi.pow_apply, pi.mul_apply, pi.bit0_apply, pi.one_apply,
    integral_const (integral ℙ X ^ 2), integral_mul_left (2 : ℝ), one_mul,
    variance, pi.pow_apply, measure_univ, ennreal.one_to_real, algebra.id.smul_eq_mul],
  ring,
end

lemma variance_le_expectation_sq [is_probability_measure (ℙ : measure Ω)]
  {X : Ω → ℝ} (hm : ae_strongly_measurable X ℙ) :
  Var[X] ≤ 𝔼[X^2] :=
begin
  by_cases hX : mem_ℒp X 2,
  { rw variance_def' hX,
    simp only [sq_nonneg, sub_le_self_iff] },
  rw [variance, evariance_eq_lintegral_of_real, ← integral_eq_lintegral_of_nonneg_ae],
  by_cases hint : integrable X, swap,
  { simp only [integral_undef hint, pi.pow_apply, pi.sub_apply, sub_zero] },
  { rw integral_undef,
    { exact integral_nonneg (λ a, sq_nonneg _) },
    { intro h,
      have A : mem_ℒp (X - λ (ω : Ω), 𝔼[X]) 2 ℙ := (mem_ℒp_two_iff_integrable_sq
        (hint.ae_strongly_measurable.sub ae_strongly_measurable_const)).2 h,
      have B : mem_ℒp (λ (ω : Ω), 𝔼[X]) 2 ℙ := mem_ℒp_const _,
      apply hX,
      convert A.add B,
      simp } },
  { exact ae_of_all _ (λ x, sq_nonneg _) },
  { exact (ae_measurable.pow_const (hm.ae_measurable.sub_const _) _).ae_strongly_measurable },
end

lemma evariance_def' [is_probability_measure (ℙ : measure Ω)]
  {X : Ω → ℝ} (hX : ae_strongly_measurable X ℙ) :
  eVar[X] = (∫⁻ ω, ‖X ω‖₊^2) - ennreal.of_real (𝔼[X]^2) :=
begin
  by_cases hℒ : mem_ℒp X 2,
  { rw [← hℒ.of_real_variance_eq, variance_def' hℒ, ennreal.of_real_sub _ (sq_nonneg _)],
    congr,
    simp_rw ← ennreal.coe_pow,
    rw lintegral_coe_eq_integral,
    { congr' 2 with ω,
      simp only [pi.pow_apply, nnreal.coe_pow, coe_nnnorm, real.norm_eq_abs, pow_bit0_abs] },
    { exact hℒ.abs.integrable_sq } },
  { symmetry,
    rw [evariance_eq_top hX hℒ, ennreal.sub_eq_top_iff],
    refine ⟨_, ennreal.of_real_ne_top⟩,
    rw [mem_ℒp, not_and] at hℒ,
    specialize hℒ hX,
    simp only [snorm_eq_lintegral_rpow_nnnorm two_ne_zero ennreal.two_ne_top, not_lt,
      top_le_iff, ennreal.to_real_bit0, ennreal.one_to_real, ennreal.rpow_two, one_div,
      ennreal.rpow_eq_top_iff, inv_lt_zero, inv_pos, zero_lt_bit0, zero_lt_one, and_true,
      or_iff_not_imp_left, not_and_distrib] at hℒ,
    exact hℒ (λ _, zero_le_two) }
end

/-- *Chebyshev's inequality* for `ℝ≥0∞`-valued variance. -/
theorem meas_ge_le_evariance_div_sq {X : Ω → ℝ}
  (hX : ae_strongly_measurable X ℙ) {c : ℝ≥0} (hc : c ≠ 0) :
  ℙ {ω | ↑c ≤ |X ω - 𝔼[X]|} ≤ eVar[X] / c ^ 2 :=
begin
  have A : (c : ℝ≥0∞) ≠ 0, { rwa [ne.def, ennreal.coe_eq_zero] },
  have B : ae_strongly_measurable (λ (ω : Ω), 𝔼[X]) ℙ := ae_strongly_measurable_const,
  convert meas_ge_le_mul_pow_snorm ℙ two_ne_zero ennreal.two_ne_top (hX.sub B) A,
  { ext ω,
    simp only [pi.sub_apply, ennreal.coe_le_coe, ← real.norm_eq_abs, ← coe_nnnorm,
      nnreal.coe_le_coe, ennreal.of_real_coe_nnreal] },
  { rw snorm_eq_lintegral_rpow_nnnorm two_ne_zero ennreal.two_ne_top,
    simp only [ennreal.to_real_bit0, ennreal.one_to_real, pi.sub_apply, one_div],
    rw [div_eq_mul_inv, ennreal.inv_pow, mul_comm, ennreal.rpow_two],
    congr,
    simp_rw [← ennreal.rpow_mul, inv_mul_cancel (two_ne_zero : (2 : ℝ) ≠ 0), ennreal.rpow_two,
      ennreal.rpow_one, evariance] }
end

/-- *Chebyshev's inequality* : one can control the deviation probability of a real random variable
from its expectation in terms of the variance. -/
theorem meas_ge_le_variance_div_sq [is_finite_measure (ℙ : measure Ω)]
  {X : Ω → ℝ} (hX : mem_ℒp X 2) {c : ℝ} (hc : 0 < c) :
  ℙ {ω | c ≤ |X ω - 𝔼[X]|} ≤ ennreal.of_real (Var[X] / c ^ 2) :=
begin
  rw [ennreal.of_real_div_of_pos (sq_pos_of_ne_zero _ hc.ne.symm), hX.of_real_variance_eq],
  convert @meas_ge_le_evariance_div_sq _ _ _ hX.1 (c.to_nnreal) (by simp [hc]),
  { simp only [real.coe_to_nnreal', max_le_iff, abs_nonneg, and_true] },
  { rw ennreal.of_real_pow hc.le,
    refl }
end

/-- The variance of the sum of two independent random variables is the sum of the variances. -/
theorem indep_fun.variance_add [is_probability_measure (ℙ : measure Ω)]
  {X Y : Ω → ℝ} (hX : mem_ℒp X 2) (hY : mem_ℒp Y 2) (h : indep_fun X Y) :
  Var[X + Y] = Var[X] + Var[Y] :=
calc
Var[X + Y] = 𝔼[λ a, (X a)^2 + (Y a)^2 + 2 * X a * Y a] - 𝔼[X+Y]^2 :
  by simp [variance_def' (hX.add hY), add_sq']
... = (𝔼[X^2] + 𝔼[Y^2] + 2 * 𝔼[X * Y]) - (𝔼[X] + 𝔼[Y])^2 :
begin
  simp only [pi.add_apply, pi.pow_apply, pi.mul_apply, mul_assoc],
  rw [integral_add, integral_add, integral_add, integral_mul_left],
  { exact hX.integrable one_le_two },
  { exact hY.integrable one_le_two },
  { exact hX.integrable_sq },
  { exact hY.integrable_sq },
  { exact hX.integrable_sq.add hY.integrable_sq },
  { apply integrable.const_mul,
    exact h.integrable_mul (hX.integrable one_le_two) (hY.integrable one_le_two) }
end
... = (𝔼[X^2] + 𝔼[Y^2] + 2 * (𝔼[X] * 𝔼[Y])) - (𝔼[X] + 𝔼[Y])^2 :
begin
  congr,
  exact h.integral_mul_of_integrable
    (hX.integrable one_le_two) (hY.integrable one_le_two),
end
... = Var[X] + Var[Y] :
  by { simp only [variance_def', hX, hY, pi.pow_apply], ring }

/-- The variance of a finite sum of pairwise independent random variables is the sum of the
variances. -/
theorem indep_fun.variance_sum [is_probability_measure (ℙ : measure Ω)]
  {ι : Type*} {X : ι → Ω → ℝ} {s : finset ι}
  (hs : ∀ i ∈ s, mem_ℒp (X i) 2) (h : set.pairwise ↑s (λ i j, indep_fun (X i) (X j))) :
  Var[∑ i in s, X i] = ∑ i in s, Var[X i] :=
begin
  classical,
  induction s using finset.induction_on with k s ks IH,
  { simp only [finset.sum_empty, variance_zero] },
  rw [variance_def' (mem_ℒp_finset_sum' _ hs), sum_insert ks, sum_insert ks],
  simp only [add_sq'],
  calc 𝔼[X k ^ 2 + (∑ i in s, X i) ^ 2 + 2 * X k * ∑ i in s, X i] - 𝔼[X k + ∑ i in s, X i] ^ 2
  = (𝔼[X k ^ 2] + 𝔼[(∑ i in s, X i) ^ 2] + 𝔼[2 * X k * ∑ i in s, X i])
    - (𝔼[X k] + 𝔼[∑ i in s, X i]) ^ 2 :
  begin
    rw [integral_add', integral_add', integral_add'],
    { exact mem_ℒp.integrable one_le_two (hs _ (mem_insert_self _ _)) },
    { apply integrable_finset_sum' _ (λ i hi, _),
      exact mem_ℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi)) },
    { exact mem_ℒp.integrable_sq (hs _ (mem_insert_self _ _)) },
    { apply mem_ℒp.integrable_sq,
      exact mem_ℒp_finset_sum' _ (λ i hi, (hs _ (mem_insert_of_mem hi))) },
    { apply integrable.add,
      { exact mem_ℒp.integrable_sq (hs _ (mem_insert_self _ _)) },
      { apply mem_ℒp.integrable_sq,
        exact mem_ℒp_finset_sum' _ (λ i hi, (hs _ (mem_insert_of_mem hi))) } },
    { rw mul_assoc,
      apply integrable.const_mul _ (2:ℝ),
      simp only [mul_sum, sum_apply, pi.mul_apply],
      apply integrable_finset_sum _ (λ i hi, _),
      apply indep_fun.integrable_mul _
        (mem_ℒp.integrable one_le_two (hs _ (mem_insert_self _ _)))
        (mem_ℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi))),
      apply h (mem_insert_self _ _) (mem_insert_of_mem hi),
      exact (λ hki, ks (hki.symm ▸ hi)) }
  end
  ... = Var[X k] + Var[∑ i in s, X i] +
    (𝔼[2 * X k * ∑ i in s, X i] - 2 * 𝔼[X k] * 𝔼[∑ i in s, X i]) :
  begin
    rw [variance_def' (hs _ (mem_insert_self _ _)),
        variance_def' (mem_ℒp_finset_sum' _ (λ i hi, (hs _ (mem_insert_of_mem hi))))],
    ring,
  end
  ... = Var[X k] + Var[∑ i in s, X i] :
  begin
    simp only [mul_assoc, integral_mul_left, pi.mul_apply, pi.bit0_apply, pi.one_apply, sum_apply,
      add_right_eq_self, mul_sum],
    rw integral_finset_sum s (λ i hi, _), swap,
    { apply integrable.const_mul _ (2:ℝ),
      apply indep_fun.integrable_mul _
        (mem_ℒp.integrable one_le_two (hs _ (mem_insert_self _ _)))
        (mem_ℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi))),
      apply h (mem_insert_self _ _) (mem_insert_of_mem hi),
      exact (λ hki, ks (hki.symm ▸ hi)) },
    rw [integral_finset_sum s
      (λ i hi, (mem_ℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi)))),
      mul_sum, mul_sum, ← sum_sub_distrib],
    apply finset.sum_eq_zero (λ i hi, _),
    rw [integral_mul_left, indep_fun.integral_mul', sub_self],
    { apply h (mem_insert_self _ _) (mem_insert_of_mem hi),
      exact (λ hki, ks (hki.symm ▸ hi)) },
    { exact mem_ℒp.ae_strongly_measurable (hs _ (mem_insert_self _ _)) },
    { exact mem_ℒp.ae_strongly_measurable (hs _ (mem_insert_of_mem hi)) }
  end
  ... = Var[X k] + ∑ i in s, Var[X i] :
    by rw IH (λ i hi, hs i (mem_insert_of_mem hi))
      (h.mono (by simp only [coe_insert, set.subset_insert]))
end

end probability_theory
