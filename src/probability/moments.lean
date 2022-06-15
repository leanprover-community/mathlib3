/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.variance

/-!
# Moments and moment generating function

## Main definitions

* `moment X p μ`: `p`th moment of `X` with respect to measure `μ`, `μ[X^p]`
* `central_moment X p μ`:`p`th central moment of `X` with respect to measure `μ`, `μ[(X - μ[X])^p]`
* `mgf X μ t`: moment generating function of `X` with respect to measure `μ`, `μ[exp(t*X)]`
* `cgf X μ t`: cumulant generating function, logarithm of the moment generating function

-/

open measure_theory filter finset

noncomputable theory

open_locale big_operators measure_theory probability_theory ennreal nnreal

namespace probability_theory

variables {Ω : Type*} {m : measurable_space Ω} {X : Ω → ℝ} {p : ℕ} {μ : measure Ω}

include m

def moment (X : Ω → ℝ) (p : ℕ) (μ : measure Ω) : ℝ := μ[X ^ p]

def central_moment (X : Ω → ℝ) (p : ℕ) (μ : measure Ω) : ℝ := μ[(X - (λ x, μ[X])) ^ p]

@[simp] lemma moment_zero (hp : p ≠ 0) : moment 0 p μ = 0 :=
by simp only [moment, hp, zero_pow', ne.def, not_false_iff, pi.zero_apply, integral_const,
  algebra.id.smul_eq_mul, mul_zero]

@[simp] lemma central_moment_zero (hp : p ≠ 0) : central_moment 0 p μ = 0 :=
by simp only [central_moment, hp, pi.zero_apply, integral_const, algebra.id.smul_eq_mul,
  mul_zero, zero_sub, pi.pow_apply, pi.neg_apply, neg_zero', zero_pow', ne.def, not_false_iff]

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

@[simp] lemma central_moment_two_eq_variance : central_moment X 2 μ = variance X μ := rfl

section moment_generating_function

variables {t : ℝ}

def mgf (X : Ω → ℝ) (μ : measure Ω) (t : ℝ) : ℝ := μ[λ ω, real.exp (t * X ω)]

def cgf (X : Ω → ℝ) (μ : measure Ω) (t : ℝ) : ℝ := real.log (mgf X μ t)

@[simp] lemma mgf_zero_fun : mgf 0 μ t = (μ set.univ).to_real :=
by simp only [mgf, pi.zero_apply, mul_zero, real.exp_zero, integral_const, algebra.id.smul_eq_mul,
  mul_one]

@[simp] lemma cgf_zero_fun : cgf 0 μ t = real.log (μ set.univ).to_real :=
by simp only [cgf, mgf_zero_fun]

@[simp] lemma mgf_const (c : ℝ) : mgf (λ _, c) μ t = (μ set.univ).to_real * real.exp (t * c) :=
by simp only [mgf, integral_const, algebra.id.smul_eq_mul]

lemma cgf_const' [is_finite_measure μ] (hμ : μ ≠ 0) (c : ℝ) :
  cgf (λ _, c) μ t = real.log (μ set.univ).to_real + t * c :=
begin
  simp only [cgf, mgf_const],
  rw real.log_mul _ (real.exp_pos _).ne',
  { rw real.log_exp _, },
  { rw [ne.def, ennreal.to_real_eq_zero_iff, measure.measure_univ_eq_zero],
    simp only [hμ, measure_ne_top μ set.univ, or_self, not_false_iff], },
end

@[simp] lemma cgf_const [is_probability_measure μ] (c : ℝ) :
  cgf (λ _, c) μ t =  t * c :=
begin
  rw cgf_const' (is_probability_measure.ne_zero μ) c,
  simp only [measure_univ, ennreal.one_to_real, real.log_one, zero_add],
end

@[simp] lemma mgf_zero : mgf X μ 0 = (μ set.univ).to_real :=
by simp only [mgf, zero_mul, real.exp_zero, integral_const, algebra.id.smul_eq_mul, mul_one]

@[simp] lemma cgf_zero : cgf X μ 0 = real.log (μ set.univ).to_real :=
by simp only [cgf, mgf_zero]

lemma mgf_undef (hX : ¬ integrable (λ ω, real.exp (t * X ω)) μ) : mgf X μ t = 0 :=
by simp only [mgf, integral_undef hX]

lemma cgf_undef (hX : ¬ integrable (λ ω, real.exp (t * X ω)) μ) : cgf X μ t = 0 :=
by simp only [cgf, mgf_undef hX, real.log_zero]

lemma mgf_nonneg : 0 ≤ mgf X μ t :=
begin
  refine integral_nonneg _,
  intro ω,
  simp only [pi.zero_apply],
  exact (real.exp_pos _).le,
end

lemma mgf_pos (hμ : μ ≠ 0) (h_int_X : integrable (λ ω, real.exp (t * X ω)) μ) : 0 < mgf X μ t :=
begin
  simp_rw mgf,
  have : ∫ (x : Ω), real.exp (t * X x) ∂μ = ∫ (x : Ω) in set.univ, real.exp (t * X x) ∂μ,
  { simp only [measure.restrict_univ], },
  rw [this, set_integral_pos_iff_support_of_nonneg_ae _ _],
  { have h_eq_univ : function.support (λ (x : Ω), real.exp (t * X x)) = set.univ,
    { ext1 x,
      simp only [function.mem_support, set.mem_univ, iff_true],
      exact (real.exp_pos _).ne', },
    rw [h_eq_univ, set.inter_univ _],
    refine ne.bot_lt _,
    simp only [hμ, ennreal.bot_eq_zero, ne.def, measure.measure_univ_eq_zero, not_false_iff], },
  { refine eventually_of_forall (λ x, _),
    rw pi.zero_apply,
    exact (real.exp_pos _).le, },
  { rwa integrable_on_univ, },
end

lemma mgf_add_of_indep_fun {X Y : Ω → ℝ} (h_indep : indep_fun X Y μ)
  (h_int_X : integrable (λ ω, real.exp (t * X ω)) μ)
  (h_int_Y : integrable (λ ω, real.exp (t * Y ω)) μ) :
  mgf (X + Y) μ t = mgf X μ t * mgf Y μ t :=
begin
  simp_rw [mgf, pi.add_apply, mul_add, real.exp_add],
  refine indep_fun.integral_mul_of_integrable' _ h_int_X h_int_Y,
  have h_meas : measurable (λ x, real.exp (t * x)) := (measurable_id'.const_mul t).exp,
  change indep_fun ((λ x, real.exp (t * x)) ∘ X) ((λ x, real.exp (t * x)) ∘ Y) μ,
  exact indep_fun.comp h_indep h_meas h_meas,
end

lemma cgf_add_of_indep_fun (hμ : μ ≠ 0) {X Y : Ω → ℝ} (h_indep : indep_fun X Y μ)
  (h_int_X : integrable (λ ω, real.exp (t * X ω)) μ)
  (h_int_Y : integrable (λ ω, real.exp (t * Y ω)) μ) :
  cgf (X + Y) μ t = cgf X μ t + cgf Y μ t :=
begin
  simp only [cgf, mgf_add_of_indep_fun h_indep h_int_X h_int_Y],
  exact real.log_mul (mgf_pos hμ h_int_X).ne' (mgf_pos hμ h_int_Y).ne',
end

end moment_generating_function

end probability_theory
