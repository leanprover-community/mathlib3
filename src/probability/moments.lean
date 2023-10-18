/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.variance

/-!
# Moments and moment generating function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `probability_theory.moment X p μ`: `p`th moment of a real random variable `X` with respect to
  measure `μ`, `μ[X^p]`
* `probability_theory.central_moment X p μ`:`p`th central moment of `X` with respect to measure `μ`,
  `μ[(X - μ[X])^p]`
* `probability_theory.mgf X μ t`: moment generating function of `X` with respect to measure `μ`,
  `μ[exp(t*X)]`
* `probability_theory.cgf X μ t`: cumulant generating function, logarithm of the moment generating
  function

## Main results

* `probability_theory.indep_fun.mgf_add`: if two real random variables `X` and `Y` are independent
  and their mgf are defined at `t`, then `mgf (X + Y) μ t = mgf X μ t * mgf Y μ t`
* `probability_theory.indep_fun.cgf_add`: if two real random variables `X` and `Y` are independent
  and their mgf are defined at `t`, then `cgf (X + Y) μ t = cgf X μ t + cgf Y μ t`
* `probability_theory.measure_ge_le_exp_cgf` and `probability_theory.measure_le_le_exp_cgf`:
  Chernoff bound on the upper (resp. lower) tail of a random variable. For `t` nonnegative such that
  the cgf exists, `ℙ(ε ≤ X) ≤ exp(- t*ε + cgf X ℙ t)`. See also
  `probability_theory.measure_ge_le_exp_mul_mgf` and
  `probability_theory.measure_le_le_exp_mul_mgf` for versions of these results using `mgf` instead
  of `cgf`.

-/

open measure_theory filter finset real

noncomputable theory

open_locale big_operators measure_theory probability_theory ennreal nnreal

namespace probability_theory

variables {Ω ι : Type*} {m : measurable_space Ω} {X : Ω → ℝ} {p : ℕ} {μ : measure Ω}

include m

/-- Moment of a real random variable, `μ[X ^ p]`. -/
def moment (X : Ω → ℝ) (p : ℕ) (μ : measure Ω) : ℝ := μ[X ^ p]

/-- Central moment of a real random variable, `μ[(X - μ[X]) ^ p]`. -/
def central_moment (X : Ω → ℝ) (p : ℕ) (μ : measure Ω) : ℝ := μ[(X - (λ x, μ[X])) ^ p]

@[simp] lemma moment_zero (hp : p ≠ 0) : moment 0 p μ = 0 :=
by simp only [moment, hp, zero_pow', ne.def, not_false_iff, pi.zero_apply, integral_const,
  algebra.id.smul_eq_mul, mul_zero]

@[simp] lemma central_moment_zero (hp : p ≠ 0) : central_moment 0 p μ = 0 :=
by simp only [central_moment, hp, pi.zero_apply, integral_const, algebra.id.smul_eq_mul,
  mul_zero, zero_sub, pi.pow_apply, pi.neg_apply, neg_zero, zero_pow', ne.def, not_false_iff]

lemma central_moment_one' [is_finite_measure μ] (h_int : integrable X μ) :
  central_moment X 1 μ = (1 - (μ set.univ).to_real) * μ[X] :=
begin
  simp only [central_moment, pi.sub_apply, pow_one],
  rw integral_sub h_int (integrable_const _),
  simp only [sub_mul, integral_const, algebra.id.smul_eq_mul, one_mul],
end

@[simp] lemma central_moment_one [is_probability_measure μ] : central_moment X 1 μ = 0 :=
begin
  by_cases h_int : integrable X μ,
  { rw central_moment_one' h_int,
    simp only [measure_univ, ennreal.one_to_real, sub_self, zero_mul], },
  { simp only [central_moment, pi.sub_apply, pow_one],
    have : ¬ integrable (λ x, X x - integral μ X) μ,
    { refine λ h_sub, h_int _,
      have h_add : X = (λ x, X x - integral μ X) + (λ x, integral μ X),
      { ext1 x, simp, },
      rw h_add,
      exact h_sub.add (integrable_const _), },
    rw integral_undef this, },
end

lemma central_moment_two_eq_variance [is_finite_measure μ] (hX : mem_ℒp X 2 μ) :
  central_moment X 2 μ = variance X μ :=
by { rw hX.variance_eq, refl, }

section moment_generating_function

variables {t : ℝ}

/-- Moment generating function of a real random variable `X`: `λ t, μ[exp(t*X)]`. -/
def mgf (X : Ω → ℝ) (μ : measure Ω) (t : ℝ) : ℝ := μ[λ ω, exp (t * X ω)]

/-- Cumulant generating function of a real random variable `X`: `λ t, log μ[exp(t*X)]`. -/
def cgf (X : Ω → ℝ) (μ : measure Ω) (t : ℝ) : ℝ := log (mgf X μ t)

@[simp] lemma mgf_zero_fun : mgf 0 μ t = (μ set.univ).to_real :=
by simp only [mgf, pi.zero_apply, mul_zero, exp_zero, integral_const, algebra.id.smul_eq_mul,
  mul_one]

@[simp] lemma cgf_zero_fun : cgf 0 μ t = log (μ set.univ).to_real :=
by simp only [cgf, mgf_zero_fun]

@[simp] lemma mgf_zero_measure : mgf X (0 : measure Ω) t = 0 :=
by simp only [mgf, integral_zero_measure]

@[simp] lemma cgf_zero_measure : cgf X (0 : measure Ω) t = 0 :=
by simp only [cgf, log_zero, mgf_zero_measure]

@[simp] lemma mgf_const' (c : ℝ) : mgf (λ _, c) μ t = (μ set.univ).to_real * exp (t * c) :=
by simp only [mgf, integral_const, algebra.id.smul_eq_mul]

@[simp] lemma mgf_const (c : ℝ) [is_probability_measure μ] : mgf (λ _, c) μ t = exp (t * c) :=
by simp only [mgf_const', measure_univ, ennreal.one_to_real, one_mul]

@[simp] lemma cgf_const' [is_finite_measure μ] (hμ : μ ≠ 0) (c : ℝ) :
  cgf (λ _, c) μ t = log (μ set.univ).to_real + t * c :=
begin
  simp only [cgf, mgf_const'],
  rw log_mul _ (exp_pos _).ne',
  { rw log_exp _, },
  { rw [ne.def, ennreal.to_real_eq_zero_iff, measure.measure_univ_eq_zero],
    simp only [hμ, measure_ne_top μ set.univ, or_self, not_false_iff], },
end

@[simp] lemma cgf_const [is_probability_measure μ] (c : ℝ) : cgf (λ _, c) μ t = t * c :=
by simp only [cgf, mgf_const, log_exp]

@[simp] lemma mgf_zero' : mgf X μ 0 = (μ set.univ).to_real :=
by simp only [mgf, zero_mul, exp_zero, integral_const, algebra.id.smul_eq_mul, mul_one]

@[simp] lemma mgf_zero [is_probability_measure μ] : mgf X μ 0 = 1 :=
by simp only [mgf_zero', measure_univ, ennreal.one_to_real]

@[simp] lemma cgf_zero' : cgf X μ 0 = log (μ set.univ).to_real :=
by simp only [cgf, mgf_zero']

@[simp] lemma cgf_zero [is_probability_measure μ] : cgf X μ 0 = 0 :=
by simp only [cgf_zero', measure_univ, ennreal.one_to_real, log_one]

lemma mgf_undef (hX : ¬ integrable (λ ω, exp (t * X ω)) μ) : mgf X μ t = 0 :=
by simp only [mgf, integral_undef hX]

lemma cgf_undef (hX : ¬ integrable (λ ω, exp (t * X ω)) μ) : cgf X μ t = 0 :=
by simp only [cgf, mgf_undef hX, log_zero]

lemma mgf_nonneg : 0 ≤ mgf X μ t :=
begin
  refine integral_nonneg _,
  intro ω,
  simp only [pi.zero_apply],
  exact (exp_pos _).le,
end

lemma mgf_pos' (hμ : μ ≠ 0) (h_int_X : integrable (λ ω, exp (t * X ω)) μ) : 0 < mgf X μ t :=
begin
  simp_rw mgf,
  have : ∫ (x : Ω), exp (t * X x) ∂μ = ∫ (x : Ω) in set.univ, exp (t * X x) ∂μ,
  { simp only [measure.restrict_univ], },
  rw [this, set_integral_pos_iff_support_of_nonneg_ae _ _],
  { have h_eq_univ : function.support (λ (x : Ω), exp (t * X x)) = set.univ,
    { ext1 x,
      simp only [function.mem_support, set.mem_univ, iff_true],
      exact (exp_pos _).ne', },
    rw [h_eq_univ, set.inter_univ _],
    refine ne.bot_lt _,
    simp only [hμ, ennreal.bot_eq_zero, ne.def, measure.measure_univ_eq_zero, not_false_iff], },
  { refine eventually_of_forall (λ x, _),
    rw pi.zero_apply,
    exact (exp_pos _).le, },
  { rwa integrable_on_univ, },
end

lemma mgf_pos [is_probability_measure μ] (h_int_X : integrable (λ ω, exp (t * X ω)) μ) :
  0 < mgf X μ t :=
mgf_pos' (is_probability_measure.ne_zero μ) h_int_X

lemma mgf_neg : mgf (-X) μ t = mgf X μ (-t) :=
by simp_rw [mgf, pi.neg_apply, mul_neg, neg_mul]

lemma cgf_neg : cgf (-X) μ t = cgf X μ (-t) := by simp_rw [cgf, mgf_neg]

/-- This is a trivial application of `indep_fun.comp` but it will come up frequently. -/
lemma indep_fun.exp_mul {X Y : Ω → ℝ} (h_indep : indep_fun X Y μ) (s t : ℝ) :
  indep_fun (λ ω, exp (s * X ω)) (λ ω, exp (t * Y ω)) μ :=
begin
  have h_meas : ∀ t, measurable (λ x, exp (t * x)) := λ t, (measurable_id'.const_mul t).exp,
  change indep_fun ((λ x, exp (s * x)) ∘ X) ((λ x, exp (t * x)) ∘ Y) μ,
  exact indep_fun.comp h_indep (h_meas s) (h_meas t),
end

lemma indep_fun.mgf_add {X Y : Ω → ℝ} (h_indep : indep_fun X Y μ)
  (hX : ae_strongly_measurable (λ ω, exp (t * X ω)) μ)
  (hY : ae_strongly_measurable (λ ω, exp (t * Y ω)) μ) :
  mgf (X + Y) μ t = mgf X μ t * mgf Y μ t :=
begin
  simp_rw [mgf, pi.add_apply, mul_add, exp_add],
  exact (h_indep.exp_mul t t).integral_mul hX hY,
end

lemma indep_fun.mgf_add' {X Y : Ω → ℝ} (h_indep : indep_fun X Y μ)
  (hX : ae_strongly_measurable X μ) (hY : ae_strongly_measurable Y μ) :
  mgf (X + Y) μ t = mgf X μ t * mgf Y μ t :=
begin
  have A : continuous (λ (x : ℝ), exp (t * x)), by continuity,
  have h'X : ae_strongly_measurable (λ ω, exp (t * X ω)) μ :=
    A.ae_strongly_measurable.comp_ae_measurable hX.ae_measurable,
  have h'Y : ae_strongly_measurable (λ ω, exp (t * Y ω)) μ :=
    A.ae_strongly_measurable.comp_ae_measurable hY.ae_measurable,
  exact h_indep.mgf_add h'X h'Y
end

lemma indep_fun.cgf_add {X Y : Ω → ℝ} (h_indep : indep_fun X Y μ)
  (h_int_X : integrable (λ ω, exp (t * X ω)) μ)
  (h_int_Y : integrable (λ ω, exp (t * Y ω)) μ) :
  cgf (X + Y) μ t = cgf X μ t + cgf Y μ t :=
begin
  by_cases hμ : μ = 0,
  { simp [hμ], },
  simp only [cgf, h_indep.mgf_add h_int_X.ae_strongly_measurable h_int_Y.ae_strongly_measurable],
  exact log_mul (mgf_pos' hμ h_int_X).ne' (mgf_pos' hμ h_int_Y).ne',
end

lemma ae_strongly_measurable_exp_mul_add {X Y : Ω → ℝ}
  (h_int_X : ae_strongly_measurable (λ ω, exp (t * X ω)) μ)
  (h_int_Y : ae_strongly_measurable (λ ω, exp (t * Y ω)) μ) :
  ae_strongly_measurable (λ ω, exp (t * (X + Y) ω)) μ :=
begin
  simp_rw [pi.add_apply, mul_add, exp_add],
  exact ae_strongly_measurable.mul h_int_X h_int_Y,
end

lemma ae_strongly_measurable_exp_mul_sum {X : ι → Ω → ℝ} {s : finset ι}
  (h_int : ∀ i ∈ s, ae_strongly_measurable (λ ω, exp (t * X i ω)) μ) :
  ae_strongly_measurable (λ ω, exp (t * (∑ i in s, X i) ω)) μ :=
begin
  classical,
  induction s using finset.induction_on with i s hi_notin_s h_rec h_int,
  { simp only [pi.zero_apply, sum_apply, sum_empty, mul_zero, exp_zero],
    exact ae_strongly_measurable_const, },
  { have : ∀ (i : ι), i ∈ s → ae_strongly_measurable (λ (ω : Ω), exp (t * X i ω)) μ,
      from λ i hi, h_int i (mem_insert_of_mem hi),
    specialize h_rec this,
    rw sum_insert hi_notin_s,
    apply ae_strongly_measurable_exp_mul_add (h_int i (mem_insert_self _ _)) h_rec }
end

lemma indep_fun.integrable_exp_mul_add {X Y : Ω → ℝ} (h_indep : indep_fun X Y μ)
  (h_int_X : integrable (λ ω, exp (t * X ω)) μ)
  (h_int_Y : integrable (λ ω, exp (t * Y ω)) μ) :
  integrable (λ ω, exp (t * (X + Y) ω)) μ :=
begin
  simp_rw [pi.add_apply, mul_add, exp_add],
  exact (h_indep.exp_mul t t).integrable_mul h_int_X h_int_Y,
end

lemma Indep_fun.integrable_exp_mul_sum [is_probability_measure μ]
  {X : ι → Ω → ℝ} (h_indep : Indep_fun (λ i, infer_instance) X μ) (h_meas : ∀ i, measurable (X i))
  {s : finset ι} (h_int : ∀ i ∈ s, integrable (λ ω, exp (t * X i ω)) μ) :
  integrable (λ ω, exp (t * (∑ i in s, X i) ω)) μ :=
begin
  classical,
  induction s using finset.induction_on with i s hi_notin_s h_rec h_int,
  { simp only [pi.zero_apply, sum_apply, sum_empty, mul_zero, exp_zero],
    exact integrable_const _, },
  { have : ∀ (i : ι), i ∈ s → integrable (λ (ω : Ω), exp (t * X i ω)) μ,
      from λ i hi, h_int i (mem_insert_of_mem hi),
    specialize h_rec this,
    rw sum_insert hi_notin_s,
    refine indep_fun.integrable_exp_mul_add _ (h_int i (mem_insert_self _ _)) h_rec,
    exact (h_indep.indep_fun_finset_sum_of_not_mem h_meas hi_notin_s).symm, },
end

lemma Indep_fun.mgf_sum [is_probability_measure μ]
  {X : ι → Ω → ℝ} (h_indep : Indep_fun (λ i, infer_instance) X μ) (h_meas : ∀ i, measurable (X i))
  (s : finset ι) :
  mgf (∑ i in s, X i) μ t = ∏ i in s, mgf (X i) μ t :=
begin
  classical,
  induction s using finset.induction_on with i s hi_notin_s h_rec h_int,
  { simp only [sum_empty, mgf_zero_fun, measure_univ, ennreal.one_to_real, prod_empty], },
  { have h_int' : ∀ (i : ι), ae_strongly_measurable (λ (ω : Ω), exp (t * X i ω)) μ,
      from λ i, ((h_meas i).const_mul t).exp.ae_strongly_measurable,
    rw [sum_insert hi_notin_s, indep_fun.mgf_add
          (h_indep.indep_fun_finset_sum_of_not_mem h_meas hi_notin_s).symm (h_int' i)
          (ae_strongly_measurable_exp_mul_sum (λ i hi, h_int' i)),
        h_rec, prod_insert hi_notin_s] }
end

lemma Indep_fun.cgf_sum [is_probability_measure μ]
  {X : ι → Ω → ℝ} (h_indep : Indep_fun (λ i, infer_instance) X μ) (h_meas : ∀ i, measurable (X i))
  {s : finset ι} (h_int : ∀ i ∈ s, integrable (λ ω, exp (t * X i ω)) μ) :
  cgf (∑ i in s, X i) μ t = ∑ i in s, cgf (X i) μ t :=
begin
  simp_rw cgf,
  rw ← log_prod _ _ (λ j hj, _),
  { rw h_indep.mgf_sum h_meas },
  { exact (mgf_pos (h_int j hj)).ne', },
end

/-- **Chernoff bound** on the upper tail of a real random variable. -/
lemma measure_ge_le_exp_mul_mgf [is_finite_measure μ] (ε : ℝ) (ht : 0 ≤ t)
  (h_int : integrable (λ ω, exp (t * X ω)) μ) :
  (μ {ω | ε ≤ X ω}).to_real ≤ exp (- t * ε) * mgf X μ t :=
begin
  cases ht.eq_or_lt with ht_zero_eq ht_pos,
  { rw ht_zero_eq.symm,
    simp only [neg_zero, zero_mul, exp_zero, mgf_zero', one_mul],
    rw ennreal.to_real_le_to_real (measure_ne_top μ _) (measure_ne_top μ _),
    exact measure_mono (set.subset_univ _), },
  calc (μ {ω | ε ≤ X ω}).to_real
      = (μ {ω | exp (t * ε) ≤ exp (t * X ω)}).to_real :
    begin
      congr' with ω,
      simp only [exp_le_exp, eq_iff_iff],
      exact ⟨λ h, mul_le_mul_of_nonneg_left h ht_pos.le, λ h, le_of_mul_le_mul_left h ht_pos⟩,
    end
  ... ≤ (exp (t * ε))⁻¹ * μ[λ ω, exp (t * X ω)] :
    begin
      have : exp (t * ε) * (μ {ω | exp (t * ε) ≤ exp (t * X ω)}).to_real
          ≤ μ[λ ω, exp (t * X ω)],
        from mul_meas_ge_le_integral_of_nonneg (λ x, (exp_pos _).le) h_int _,
      rwa [mul_comm (exp (t * ε))⁻¹, ← div_eq_mul_inv, le_div_iff' (exp_pos _)],
    end
  ... = exp (- t * ε) * mgf X μ t : by { rw [neg_mul, exp_neg], refl, },
end

/-- **Chernoff bound** on the lower tail of a real random variable. -/
lemma measure_le_le_exp_mul_mgf [is_finite_measure μ] (ε : ℝ) (ht : t ≤ 0)
  (h_int : integrable (λ ω, exp (t * X ω)) μ) :
  (μ {ω | X ω ≤ ε}).to_real ≤ exp (- t * ε) * mgf X μ t :=
begin
  rw [← neg_neg t, ← mgf_neg, neg_neg, ← neg_mul_neg (-t)],
  refine eq.trans_le _ (measure_ge_le_exp_mul_mgf (-ε) (neg_nonneg.mpr ht) _),
  { congr' with ω,
    simp only [pi.neg_apply, neg_le_neg_iff], },
  { simp_rw [pi.neg_apply, neg_mul_neg],
    exact h_int, },
end

/-- **Chernoff bound** on the upper tail of a real random variable. -/
lemma measure_ge_le_exp_cgf [is_finite_measure μ] (ε : ℝ) (ht : 0 ≤ t)
  (h_int : integrable (λ ω, exp (t * X ω)) μ) :
  (μ {ω | ε ≤ X ω}).to_real ≤ exp (- t * ε + cgf X μ t) :=
begin
  refine (measure_ge_le_exp_mul_mgf ε ht h_int).trans _,
  rw exp_add,
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le,
end

/-- **Chernoff bound** on the lower tail of a real random variable. -/
lemma measure_le_le_exp_cgf [is_finite_measure μ] (ε : ℝ) (ht : t ≤ 0)
  (h_int : integrable (λ ω, exp (t * X ω)) μ) :
  (μ {ω | X ω ≤ ε}).to_real ≤ exp (- t * ε + cgf X μ t) :=
begin
  refine (measure_le_le_exp_mul_mgf ε ht h_int).trans _,
  rw exp_add,
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le,
end

end moment_generating_function

end probability_theory
