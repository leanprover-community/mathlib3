/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import probability.notation
import probability.integration

/-!
# Variance of random variables

We define the variance of a real-valued random variable as `Var[X] = 𝔼[(X - 𝔼[X])^2]` (in the
`probability_theory` locale).

We prove the basic properties of the variance:
* `variance_le_expectation_sq`: the inequality `Var[X] ≤ 𝔼[X^2]`.
* `meas_ge_le_variance_div_sq`: Chebyshev's inequality, i.e.,
      `ℙ {ω | c ≤ |X ω - 𝔼[X]|} ≤ ennreal.of_real (Var[X] / c ^ 2)`.
* `indep_fun.variance_add`: the variance of the sum of two independent random variables is the sum
  of the variances.
* `indep_fun.variance_sum`: the variance of a finite sum of pairwise independent random variables is
  the sum of the variances.
-/

open measure_theory filter finset

noncomputable theory

open_locale big_operators measure_theory probability_theory ennreal nnreal

namespace probability_theory

def evariance {Ω : Type*} {m : measurable_space Ω} (f : Ω → ℝ) (μ : measure Ω) : ℝ≥0∞ :=
∫⁻ ω, ∥f ω - μ[f]∥₊^2 ∂μ

/-- The variance of a random variable is `𝔼[X^2] - 𝔼[X]^2` or, equivalently, `𝔼[(X - 𝔼[X])^2]`. We
use the latter as the definition, to ensure better behavior even in garbage situations. -/
def variance {Ω : Type*} {m : measurable_space Ω} (f : Ω → ℝ) (μ : measure Ω) : ℝ :=
(evariance f μ).to_real

section move

lemma real.to_nnreal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : r.to_nnreal = ⟨r, hr⟩ :=
by simp_rw [real.to_nnreal, max_eq_left hr]

lemma real.to_nnreal_nonneg_eq_nnnorm {r : ℝ} (hr : 0 ≤ r) : r.to_nnreal = ∥r∥₊ :=
begin
  rw real.to_nnreal_of_nonneg hr,
  congr,
  rw [real.norm_eq_abs, abs_of_nonneg hr],
end

lemma real.to_nnreal_mul_nnnorm {r : ℝ} (s : ℝ) (hr : 0 ≤ r) : r.to_nnreal * ∥s∥₊ = ∥r * s∥₊ :=
begin
  rw real.to_nnreal_of_nonneg hr,
  simp only [nnnorm_mul, mul_eq_mul_right_iff],
  refine or.inl (nnreal.eq _),
  simp only [subtype.coe_mk, coe_nnnorm, real.norm_eq_abs, abs_of_nonneg hr]
end

end move

lemma evariance_eq_lintegral_of_real {Ω : Type*} {m : measurable_space Ω}
  (f : Ω → ℝ) (μ : measure Ω) :
  evariance f μ = ∫⁻ ω, ennreal.of_real ((f ω - μ[f])^2) ∂μ :=
begin
  rw evariance,
  congr,
  ext1 ω,
  rw [pow_two, ← ennreal.coe_mul, ← nnnorm_mul, ← pow_two],
  congr,
  exact (real.to_nnreal_nonneg_eq_nnnorm $ sq_nonneg _).symm,
end

lemma variance_eq_of_integral_eq_zero {Ω : Type*} {m : measurable_space Ω}
  {f : Ω → ℝ} {μ : measure Ω} (hf : mem_ℒp f 2 μ) (hfint : μ[f] = 0) :
  variance f μ = μ[f^2] :=
begin
  rw [variance, evariance_eq_lintegral_of_real, ← of_real_integral_eq_lintegral_of_real,
    ennreal.to_real_of_real];
  simp_rw [hfint, sub_zero],
  { refl },
  { exact integral_nonneg (λ ω, pow_two_nonneg _) },
  { convert hf.integrable_norm_rpow ennreal.two_ne_zero ennreal.two_ne_top,
    ext ω,
    simp only [pi.sub_apply, real.norm_eq_abs, ennreal.to_real_bit0, ennreal.one_to_real,
      real.rpow_two, pow_bit0_abs] },
  { exact ae_of_all _ (λ ω, pow_two_nonneg _) }
end

lemma variance_eq {Ω : Type*} {m : measurable_space Ω} {f : Ω → ℝ} {μ : measure Ω}
  [is_finite_measure μ] (hf : mem_ℒp f 2 μ) :
  variance f μ = μ[(f - (λ ω, μ[f]))^2] :=
begin
  rw [variance, evariance_eq_lintegral_of_real, ← of_real_integral_eq_lintegral_of_real,
    ennreal.to_real_of_real],
  { refl },
  { exact integral_nonneg (λ ω, pow_two_nonneg _) },
  { convert (hf.sub $ mem_ℒp_const (μ[f])).integrable_norm_rpow
      ennreal.two_ne_zero ennreal.two_ne_top,
    ext ω,
    simp only [pi.sub_apply, real.norm_eq_abs, ennreal.to_real_bit0, ennreal.one_to_real,
      real.rpow_two, pow_bit0_abs] },
  { exact ae_of_all _ (λ ω, pow_two_nonneg _) }
end

@[simp] lemma evariance_zero {Ω : Type*} {m : measurable_space Ω} {μ : measure Ω} :
  evariance 0 μ = 0 :=
by simp [evariance]

lemma evariance_eq_zero_iff {Ω : Type*} {m : measurable_space Ω}
  {f : Ω → ℝ} {μ : measure Ω} (hf : ae_measurable f μ) :
  evariance f μ = 0 ↔ f =ᵐ[μ] λ ω, μ[f] :=
begin
  rw [evariance, lintegral_eq_zero_iff'],
  split; intro hf; filter_upwards [hf] with ω hω,
  { simp only [pi.zero_apply, pow_eq_zero_iff, nat.succ_pos', ennreal.coe_eq_zero,
      nnnorm_eq_zero, sub_eq_zero] at hω,
    exact hω },
  { rw hω,
    simp },
  { measurability }
end

@[simp] lemma evariance_nonneg {Ω : Type*} {m : measurable_space Ω} (μ : measure Ω) :
  0 ≤ evariance 0 μ :=
zero_le _

lemma evariance_mul {Ω : Type*} {m : measurable_space Ω} (c : ℝ) (f : Ω → ℝ) (μ : measure Ω) :
  evariance (λ ω, c * f ω) μ = ennreal.of_real (c^2) * evariance f μ :=
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

localized "notation (name := probability_theory.variance) `eVar[` X `]` :=
  probability_theory.evariance X measure_theory.measure_space.volume" in probability_theory

variables {Ω : Type*} [measure_space Ω] [is_probability_measure (volume : measure Ω)]

theorem meas_ge_le_evariance_div_sq {X : Ω → ℝ}
  (hX : ae_strongly_measurable X ℙ) {c : ℝ≥0} (hc : c ≠ 0) :
  ℙ {ω | ↑c ≤ |X ω - 𝔼[X]|} ≤ eVar[X] / c ^ 2 :=
begin
  have A : (c : ℝ≥0∞) ≠ 0, { rwa [ne.def, ennreal.coe_eq_zero] },
  have B : ae_strongly_measurable (λ (ω : Ω), 𝔼[X]) ℙ := ae_strongly_measurable_const,
  convert meas_ge_le_mul_pow_snorm ℙ ennreal.two_ne_zero ennreal.two_ne_top (hX.sub B) A,
  { ext ω,
    simp only [pi.sub_apply, ennreal.coe_le_coe, ← real.norm_eq_abs, ← coe_nnnorm,
      nnreal.coe_le_coe, ennreal.of_real_coe_nnreal] },
  { rw snorm_eq_lintegral_rpow_nnnorm ennreal.two_ne_zero ennreal.two_ne_top,
    simp only [ennreal.to_real_bit0, ennreal.one_to_real, pi.sub_apply, one_div],
    rw [div_eq_mul_inv, ennreal.inv_pow, mul_comm, ennreal.rpow_two],
    congr,
    simp_rw [← ennreal.rpow_mul, inv_mul_cancel (two_ne_zero : (2 : ℝ) ≠ 0), ennreal.rpow_two,
      ennreal.rpow_one, evariance] }
end


#exit
@[simp] lemma variance_zero {Ω : Type*} {m : measurable_space Ω} (μ : measure Ω) :
  variance 0 μ = 0 :=
by simp only [variance, evariance, pi.zero_apply, integral_const, algebra.id.smul_eq_mul, mul_zero,
  tsub_zero, zero_pow', ne.def, bit0_eq_zero, nat.one_ne_zero, not_false_iff, ennreal.of_real_zero,
  lintegral_const, zero_mul, ennreal.zero_to_real]

lemma variance_nonneg {Ω : Type*} {m : measurable_space Ω} (f : Ω → ℝ) (μ : measure Ω) :
  0 ≤ variance f μ :=
integral_nonneg (λ ω, sq_nonneg _)

lemma variance_mul {Ω : Type*} {m : measurable_space Ω} (c : ℝ) (f : Ω → ℝ) (μ : measure Ω) :
  variance (λ ω, c * f ω) μ = c^2 * variance f μ :=
calc
variance (λ ω, c * f ω) μ
    = ∫ x, (c * f x - ∫ y, c * f y ∂μ) ^ 2 ∂μ : rfl
... = ∫ x, (c * (f x - ∫ y, f y ∂μ)) ^ 2 ∂μ :
  by { congr' 1 with x, simp_rw [integral_mul_left, mul_sub] }
... = c^2 * variance f μ :
  by { simp_rw [mul_pow, integral_mul_left], refl }

lemma variance_smul {Ω : Type*} {m : measurable_space Ω} (c : ℝ) (f : Ω → ℝ) (μ : measure Ω) :
  variance (c • f) μ = c^2 * variance f μ :=
variance_mul c f μ

lemma variance_smul' {A : Type*} [comm_semiring A] [algebra A ℝ]
  {Ω : Type*} {m : measurable_space Ω} (c : A) (f : Ω → ℝ) (μ : measure Ω) :
  variance (c • f) μ = c^2 • variance f μ :=
begin
  convert variance_smul (algebra_map A ℝ c) f μ,
  { ext1 x, simp only [algebra_map_smul], },
  { simp only [algebra.smul_def, map_pow], }
end

localized "notation (name := probability_theory.variance) `Var[` X `]` :=
  probability_theory.variance X measure_theory.measure_space.volume" in probability_theory

variables {Ω : Type*} [measure_space Ω] [is_probability_measure (volume : measure Ω)]

lemma variance_def' {X : Ω → ℝ} (hX : mem_ℒp X 2) :
  Var[X] = 𝔼[X^2] - 𝔼[X]^2 :=
begin
  rw [variance, sub_sq', integral_sub', integral_add'], rotate,
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

lemma variance_le_expectation_sq {X : Ω → ℝ} :
  Var[X] ≤ 𝔼[X^2] :=
begin
  by_cases h_int : integrable X, swap,
  { simp only [variance, integral_undef h_int, pi.pow_apply, pi.sub_apply, sub_zero] },
  by_cases hX : mem_ℒp X 2,
  { rw variance_def' hX,
    simp only [sq_nonneg, sub_le_self_iff] },
  { rw [variance, integral_undef],
    { exact integral_nonneg (λ a, sq_nonneg _) },
    { assume h,
      have A : mem_ℒp (X - λ (ω : Ω), 𝔼[X]) 2 ℙ := (mem_ℒp_two_iff_integrable_sq
        (h_int.ae_strongly_measurable.sub ae_strongly_measurable_const)).2 h,
      have B : mem_ℒp (λ (ω : Ω), 𝔼[X]) 2 ℙ := mem_ℒp_const _,
      apply hX,
      convert A.add B,
      simp } }
end

/-- *Chebyshev's inequality* : one can control the deviation probability of a real random variable
from its expectation in terms of the variance. -/
theorem meas_ge_le_variance_div_sq {X : Ω → ℝ} (hX : mem_ℒp X 2) {c : ℝ} (hc : 0 < c) :
  ℙ {ω | c ≤ |X ω - 𝔼[X]|} ≤ ennreal.of_real (Var[X] / c ^ 2) :=
begin
  have A : (ennreal.of_real c : ℝ≥0∞) ≠ 0,
    by simp only [hc, ne.def, ennreal.of_real_eq_zero, not_le],
  have B : ae_strongly_measurable (λ (ω : Ω), 𝔼[X]) ℙ := ae_strongly_measurable_const,
  convert meas_ge_le_mul_pow_snorm ℙ ennreal.two_ne_zero ennreal.two_ne_top
    (hX.ae_strongly_measurable.sub B) A,
  { ext ω,
    set d : ℝ≥0 := ⟨c, hc.le⟩ with hd,
    have cd : c = d, by simp only [subtype.coe_mk],
    simp only [pi.sub_apply, ennreal.coe_le_coe, ← real.norm_eq_abs, ← coe_nnnorm,
      nnreal.coe_le_coe, cd, ennreal.of_real_coe_nnreal] },
  { rw (hX.sub (mem_ℒp_const _)).snorm_eq_integral_rpow_norm
      ennreal.two_ne_zero ennreal.two_ne_top,
    simp only [pi.sub_apply, ennreal.to_real_bit0, ennreal.one_to_real],
    rw ennreal.of_real_rpow_of_nonneg _ zero_le_two, rotate,
    { apply real.rpow_nonneg_of_nonneg,
      exact integral_nonneg (λ x, real.rpow_nonneg_of_nonneg (norm_nonneg _) _) },
    rw [variance, ← real.rpow_mul, inv_mul_cancel], rotate,
    { exact two_ne_zero },
    { exact integral_nonneg (λ x, real.rpow_nonneg_of_nonneg (norm_nonneg _) _) },
    simp only [pi.pow_apply, pi.sub_apply, real.rpow_two, real.rpow_one, real.norm_eq_abs,
      pow_bit0_abs, ennreal.of_real_inv_of_pos hc, ennreal.rpow_two],
    rw [← ennreal.of_real_pow (inv_nonneg.2 hc.le), ← ennreal.of_real_mul (sq_nonneg _),
      div_eq_inv_mul, inv_pow] }
end

/-- The variance of the sum of two independent random variables is the sum of the variances. -/
theorem indep_fun.variance_add {X Y : Ω → ℝ}
  (hX : mem_ℒp X 2) (hY : mem_ℒp Y 2) (h : indep_fun X Y) :
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
theorem indep_fun.variance_sum {ι : Type*} {X : ι → Ω → ℝ} {s : finset ι}
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
      apply integrable.const_mul _ 2,
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
    { apply integrable.const_mul _ 2,
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
