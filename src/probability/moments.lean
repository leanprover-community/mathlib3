/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.variance

/-!
# Moments and moment generating function

## Main definitions

* `moment X p μ`: `p`th moment of a real random variable `X` with respect to measure `μ`, `μ[X^p]`
* `central_moment X p μ`:`p`th central moment of `X` with respect to measure `μ`, `μ[(X - μ[X])^p]`
* `mgf X μ t`: moment generating function of `X` with respect to measure `μ`, `μ[exp(t*X)]`
* `cgf X μ t`: cumulant generating function, logarithm of the moment generating function

## Main results

* `indep_fun.mgf_add`: if two real random variables `X` and `Y` are independent and their mgf are
  defined at `t`, then `mgf (X + Y) μ t = mgf X μ t * mgf Y μ t`
* `indep_fun.cgf_add`: if two real random variables `X` and `Y` are independent and their mgf are
  defined at `t`, then `cgf (X + Y) μ t = cgf X μ t + cgf Y μ t`
* `measure_ge_le_exp_cgf` and `measure_le_le_exp_cgf`: Chernoff bound on the upper (resp.
  lower) tail of a random variable. For `t` nonnegative such that the cgf exists,
  `ℙ(ε ≤ X) ≤ exp( - t*ε + cfg X ℙ t)`. See also `measure_ge_le_exp_mul_mgf` and
  `measure_le_le_exp_mul_mgf` for versions of these results using `mgf` instead of `cgf`.

-/

open measure_theory filter finset

noncomputable theory

open_locale big_operators measure_theory probability_theory ennreal nnreal

namespace probability_theory

variables {Ω : Type*} {m : measurable_space Ω} {X : Ω → ℝ} {p : ℕ} {μ : measure Ω}

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

/-- Moment generating function of a real random variable `X`: `λ t, μ[exp(t*X)]`. -/
def mgf (X : Ω → ℝ) (μ : measure Ω) (t : ℝ) : ℝ := μ[λ ω, real.exp (t * X ω)]

/-- Cumulant generating function of a real random variable `X`: `λ t, log μ[exp(t*X)]`. -/
def cgf (X : Ω → ℝ) (μ : measure Ω) (t : ℝ) : ℝ := real.log (mgf X μ t)

@[simp] lemma mgf_zero_fun : mgf 0 μ t = (μ set.univ).to_real :=
by simp only [mgf, pi.zero_apply, mul_zero, real.exp_zero, integral_const, algebra.id.smul_eq_mul,
  mul_one]

@[simp] lemma cgf_zero_fun : cgf 0 μ t = real.log (μ set.univ).to_real :=
by simp only [cgf, mgf_zero_fun]

@[simp] lemma mgf_zero_measure : mgf X (0 : measure Ω) t = 0 :=
by simp only [mgf, integral_zero_measure]

@[simp] lemma cgf_zero_measure : cgf X (0 : measure Ω) t = 0 :=
by simp only [cgf, real.log_zero, mgf_zero_measure]

@[simp] lemma mgf_const' (c : ℝ) : mgf (λ _, c) μ t = (μ set.univ).to_real * real.exp (t * c) :=
by simp only [mgf, integral_const, algebra.id.smul_eq_mul]

@[simp] lemma mgf_const (c : ℝ) [is_probability_measure μ] : mgf (λ _, c) μ t = real.exp (t * c) :=
by simp only [mgf_const', measure_univ, ennreal.one_to_real, one_mul]

@[simp] lemma cgf_const' [is_finite_measure μ] (hμ : μ ≠ 0) (c : ℝ) :
  cgf (λ _, c) μ t = real.log (μ set.univ).to_real + t * c :=
begin
  simp only [cgf, mgf_const'],
  rw real.log_mul _ (real.exp_pos _).ne',
  { rw real.log_exp _, },
  { rw [ne.def, ennreal.to_real_eq_zero_iff, measure.measure_univ_eq_zero],
    simp only [hμ, measure_ne_top μ set.univ, or_self, not_false_iff], },
end

@[simp] lemma cgf_const [is_probability_measure μ] (c : ℝ) : cgf (λ _, c) μ t = t * c :=
by simp only [cgf, mgf_const, real.log_exp]

@[simp] lemma mgf_zero' : mgf X μ 0 = (μ set.univ).to_real :=
by simp only [mgf, zero_mul, real.exp_zero, integral_const, algebra.id.smul_eq_mul, mul_one]

@[simp] lemma mgf_zero [is_probability_measure μ] : mgf X μ 0 = 1 :=
by simp only [mgf_zero', measure_univ, ennreal.one_to_real]

@[simp] lemma cgf_zero' : cgf X μ 0 = real.log (μ set.univ).to_real :=
by simp only [cgf, mgf_zero']

@[simp] lemma cgf_zero [is_probability_measure μ] : cgf X μ 0 = 0 :=
by simp only [cgf_zero', measure_univ, ennreal.one_to_real, real.log_one]

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

lemma mgf_pos' (hμ : μ ≠ 0) (h_int_X : integrable (λ ω, real.exp (t * X ω)) μ) : 0 < mgf X μ t :=
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

lemma mgf_pos [is_probability_measure μ] (h_int_X : integrable (λ ω, real.exp (t * X ω)) μ) :
  0 < mgf X μ t :=
mgf_pos' (is_probability_measure.ne_zero μ) h_int_X

lemma mgf_neg : mgf (-X) μ t = mgf X μ (-t) :=
by simp_rw [mgf, pi.neg_apply, mul_neg, neg_mul]

lemma cgf_neg : cgf (-X) μ t = cgf X μ (-t) := by simp_rw [cgf, mgf_neg]

/-- This is a trivial application of `indep_fun.comp` but it will come up frequently. -/
lemma indep_fun.exp_mul {X Y : Ω → ℝ} (h_indep : indep_fun X Y μ) (t : ℝ) :
  indep_fun (λ ω, real.exp (t * X ω)) (λ ω, real.exp (t * Y ω)) μ :=
begin
  have h_meas : measurable (λ x, real.exp (t * x)) := (measurable_id'.const_mul t).exp,
  change indep_fun ((λ x, real.exp (t * x)) ∘ X) ((λ x, real.exp (t * x)) ∘ Y) μ,
  exact indep_fun.comp h_indep h_meas h_meas,
end

lemma indep_fun.mgf_add {X Y : Ω → ℝ} (h_indep : indep_fun X Y μ)
  (h_int_X : integrable (λ ω, real.exp (t * X ω)) μ)
  (h_int_Y : integrable (λ ω, real.exp (t * Y ω)) μ) :
  mgf (X + Y) μ t = mgf X μ t * mgf Y μ t :=
begin
  simp_rw [mgf, pi.add_apply, mul_add, real.exp_add],
  exact (h_indep.exp_mul t).integral_mul_of_integrable' h_int_X h_int_Y,
end

lemma indep_fun.cgf_add {X Y : Ω → ℝ} (h_indep : indep_fun X Y μ)
  (h_int_X : integrable (λ ω, real.exp (t * X ω)) μ)
  (h_int_Y : integrable (λ ω, real.exp (t * Y ω)) μ) :
  cgf (X + Y) μ t = cgf X μ t + cgf Y μ t :=
begin
  by_cases hμ : μ = 0,
  { simp [hμ], },
  simp only [cgf, h_indep.mgf_add h_int_X h_int_Y],
  exact real.log_mul (mgf_pos' hμ h_int_X).ne' (mgf_pos' hμ h_int_Y).ne',
end

lemma indep_fun.integrable_exp_mul_add {X Y : Ω → ℝ} (h_indep : indep_fun X Y μ)
  (h_int_X : integrable (λ ω, real.exp (t * X ω)) μ)
  (h_int_Y : integrable (λ ω, real.exp (t * Y ω)) μ) :
  integrable (λ ω, real.exp (t * (X + Y) ω)) μ :=
begin
  simp_rw [pi.add_apply, mul_add, real.exp_add],
  exact (h_indep.exp_mul t).integrable_mul h_int_X h_int_Y,
end

lemma indep_sets.bUnion {α ι} {m : measurable_space α} {s : ι → set (set α)} {s' : set (set α)}
  {μ : measure α} {t : finset ι} (hyp : ∀ n ∈ t, indep_sets (s n) s' μ) :
  indep_sets (⋃ n (h : n ∈ t), s n) s' μ :=
begin
  intros t1 t2 ht1 ht2,
  simp_rw [set.mem_Union] at ht1,
  rcases ht1 with ⟨n, hnt, ht1⟩,
  exact hyp n hnt t1 t2 ht1 ht2,
end

lemma indep.inf {α} {m1 m1' m2 m : measurable_space α} {μ : measure α} (h : indep m1 m2 μ) :
  indep (m1 ⊓ m1') m2 μ :=
indep_sets.inter _ h

lemma Indep_fun.prod_mk {ι : Type*} [is_probability_measure μ]
  {X : ι → Ω → ℝ} (h_meas : ∀ i, measurable (X i))
  (h_indep : Indep_fun (λ i, infer_instance) X μ) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
  indep_fun (λ ω, (X i ω, X j ω)) (X k) μ :=
begin
  classical,
  have h_right : X k = (λ p : (Π j : ({k} : finset ι), ℝ), p ⟨k, finset.mem_singleton_self k⟩)
    ∘ (λ a (j : ({k} : finset ι)), X j a) := rfl,
  have h_meas_right : measurable
      (λ p : (Π j : ({k} : finset ι), ℝ), p ⟨k, finset.mem_singleton_self k⟩),
    from measurable_pi_apply ⟨k, mem_singleton_self k⟩,
  let s : finset ι := {i, j},
  have h_left : (λ ω, (X i ω, X j ω))
    = (λ p : (Π l : s, ℝ),
        (p ⟨i, mem_insert_self i _⟩, p ⟨j, mem_insert_of_mem (mem_singleton_self _)⟩))
      ∘ (λ a (j : s), X j a),
  { ext1 a,
    simp only [subtype.coe_mk, prod.mk.inj_iff, eq_self_iff_true, and_self], },
  have h_meas_left : measurable (λ p : (Π l : s, ℝ),
        (p ⟨i, mem_insert_self i _⟩, p ⟨j, mem_insert_of_mem (mem_singleton_self _)⟩)),
  { exact measurable.prod (measurable_pi_apply ⟨i, mem_insert_self i {j}⟩)
      (measurable_pi_apply ⟨j, mem_insert_of_mem (mem_singleton_self j)⟩), },
  rw [h_left, h_right],
  refine (h_indep.indep_fun_finset s {k} _ h_meas).comp h_meas_left h_meas_right,
  intros x hx,
  simp only [inf_eq_inter, mem_inter, mem_insert, mem_singleton] at hx,
  simp only [bot_eq_empty, not_mem_empty],
  cases hx.1 with hx_eq hx_eq; rw hx_eq at hx,
  { exact hik hx.2, },
  { exact hjk hx.2, },
end

lemma indep_fun.add {ι : Type*} [is_probability_measure μ]
  {X : ι → Ω → ℝ} (h_meas : ∀ i, measurable (X i))
  (h : Indep_fun (λ i, infer_instance) X μ) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
  indep_fun (X i + X j) (X k) μ :=
begin
  have : indep_fun (λ ω, (X i ω, X j ω)) (X k) μ := h.prod_mk h_meas i j k hik hjk,
  change indep_fun ((λ p : ℝ × ℝ, p.fst + p.snd) ∘ (λ ω, (X i ω, X j ω))) (id ∘ (X k)) μ,
  exact indep_fun.comp this (measurable_fst.add measurable_snd) measurable_id,
end

lemma Indep_fun.indep_fun_finset_of_not_mem {ι : Type*} [is_probability_measure μ]
  {X : ι → Ω → ℝ} (h_indep : Indep_fun (λ i, infer_instance) X μ) (h_meas : ∀ i, measurable (X i))
  {s : finset ι} {i : ι} (hi : i ∉ s) :
  indep_fun (X i) (∑ j in s, X j) μ :=
begin
  classical,
  have h_left : X i = (λ p : (Π j : ({i} : finset ι), ℝ), p ⟨i, finset.mem_singleton_self i⟩)
    ∘ (λ a (j : ({i} : finset ι)), X j a) := rfl,
  have h_meas_left : measurable
      (λ p : (Π j : ({i} : finset ι), ℝ), p ⟨i, finset.mem_singleton_self i⟩),
    from measurable_pi_apply ⟨i, mem_singleton_self i⟩,
  have h_right : (∑ j in s, X j) = (λ p : (Π j : s, ℝ), ∑ j, p j) ∘ (λ a (j : s), X j a),
  { ext1 a,
    simp only [function.comp_app],
    have : (∑ (j : ↥s), X ↑j a) = (∑ (j : ↥s), X ↑j) a, by rw finset.sum_apply,
    rw [this, sum_coe_sort], },
  have h_meas_right : measurable (λ p : (Π j : s, ℝ), ∑ j, p j),
    from univ.measurable_sum (λ (j : ↥s) (H : j ∈ univ), measurable_pi_apply j),
  rw [h_left, h_right],
  exact (h_indep.indep_fun_finset {i} s (disjoint_singleton_left.mpr hi) h_meas).comp
    h_meas_left h_meas_right,
end

lemma Indep_fun.integrable_exp_mul_sum {ι : Type*} [is_probability_measure μ]
  {X : ι → Ω → ℝ} (h_indep : Indep_fun (λ i, infer_instance) X μ) (h_meas : ∀ i, measurable (X i))
  {s : finset ι} (h_int : ∀ i ∈ s, integrable (λ ω, real.exp (t * X i ω)) μ) :
  integrable (λ ω, real.exp (t * (∑ i in s, X i) ω)) μ :=
begin
  classical,
  revert h_int,
  refine finset.induction_on s (λ h, _) (λ i s hi_notin_s h_rec h_int, _),
  { simp only [pi.zero_apply, sum_apply, sum_empty, mul_zero, real.exp_zero],
    exact integrable_const _, },
  { have : ∀ (i : ι), i ∈ s → integrable (λ (ω : Ω), real.exp (t * X i ω)) μ,
      from λ i hi, h_int i (mem_insert_of_mem hi),
    specialize h_rec this,
    rw sum_insert hi_notin_s,
    refine indep_fun.integrable_exp_mul_add _ (h_int i (mem_insert_self _ _)) h_rec,
    exact h_indep.indep_fun_finset_of_not_mem h_meas hi_notin_s, },
end

lemma Indep_fun.mgf_sum {ι : Type*} [is_probability_measure μ]
  {X : ι → Ω → ℝ} (h_indep : Indep_fun (λ i, infer_instance) X μ) (h_meas : ∀ i, measurable (X i))
  {s : finset ι} (h_int : ∀ i ∈ s, integrable (λ ω, real.exp (t * X i ω)) μ) :
  mgf (∑ i in s, X i) μ t = ∏ i in s, mgf (X i) μ t :=
begin
  classical,
  revert h_int,
  refine finset.induction_on s (λ h, _) (λ i s hi_notin_s h_rec h_int, _),
  { simp only [sum_empty, mgf_zero_fun, measure_univ, ennreal.one_to_real, prod_empty], },
  { have h_int' : ∀ (i : ι), i ∈ s → integrable (λ (ω : Ω), real.exp (t * X i ω)) μ,
      from λ i hi, h_int i (mem_insert_of_mem hi),
    rw [sum_insert hi_notin_s, indep_fun.mgf_add
        (h_indep.indep_fun_finset_of_not_mem h_meas hi_notin_s)
        (h_int i (mem_insert_self _ _)) (h_indep.integrable_exp_mul_sum h_meas h_int'),
      h_rec h_int', prod_insert hi_notin_s], },
end

lemma Indep_fun.cgf_sum {ι : Type*} [is_probability_measure μ]
  {X : ι → Ω → ℝ} (h_indep : Indep_fun (λ i, infer_instance) X μ) (h_meas : ∀ i, measurable (X i))
  {s : finset ι} (h_int : ∀ i ∈ s, integrable (λ ω, real.exp (t * X i ω)) μ) :
  cgf (∑ i in s, X i) μ t = ∑ i in s, cgf (X i) μ t :=
begin
  simp_rw cgf,
  by_cases hμ : μ = 0,
  { simp [hμ], },
  rw ← real.log_prod _ _ (λ j hj, _),
  { rw h_indep.mgf_sum h_meas h_int, },
  { exact (mgf_pos (h_int j hj)).ne', },
end

/-- **Chernoff bound** on the upper tail of a real random variable. -/
lemma measure_ge_le_exp_mul_mgf [is_finite_measure μ] (ε : ℝ) (ht : 0 ≤ t)
  (h_int : integrable (λ ω, real.exp (t * X ω)) μ) :
  (μ {ω | ε ≤ X ω}).to_real ≤ real.exp(- t * ε) * mgf X μ t :=
begin
  rw le_iff_eq_or_lt at ht,
  cases ht with ht_zero_eq ht_pos,
  { rw ht_zero_eq.symm,
    simp only [neg_zero', zero_mul, real.exp_zero, mgf_zero', one_mul],
    rw ennreal.to_real_le_to_real (measure_ne_top μ _) (measure_ne_top μ _),
    exact measure_mono (set.subset_univ _), },
  calc (μ {ω | ε ≤ X ω}).to_real
      = (μ {ω | real.exp (t * ε) ≤ real.exp (t * X ω)}).to_real :
    begin
      congr' with ω,
      simp only [real.exp_le_exp, eq_iff_iff],
      exact ⟨λ h, mul_le_mul_of_nonneg_left h ht_pos.le, λ h, le_of_mul_le_mul_left h ht_pos⟩,
    end
  ... ≤ (real.exp (t * ε))⁻¹ * μ[λ ω, real.exp (t * X ω)] :
    begin
      have : real.exp (t * ε) * (μ {ω | real.exp (t * ε) ≤ real.exp (t * X ω)}).to_real
          ≤ μ[λ ω, real.exp (t * X ω)],
        from mul_meas_ge_le_integral_of_nonneg (λ x, (real.exp_pos _).le) h_int _,
      rwa [mul_comm (real.exp (t * ε))⁻¹, ← div_eq_mul_inv, le_div_iff' (real.exp_pos _)],
    end
  ... = real.exp(- t * ε) * mgf X μ t : by { rw [neg_mul, real.exp_neg], refl, },
end

/-- **Chernoff bound** on the lower tail of a real random variable. -/
lemma measure_le_le_exp_mul_mgf [is_finite_measure μ] (ε : ℝ) (ht : t ≤ 0)
  (h_int : integrable (λ ω, real.exp (t * X ω)) μ) :
  (μ {ω | X ω ≤ ε}).to_real ≤ real.exp(- t * ε) * mgf X μ t :=
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
  (h_int : integrable (λ ω, real.exp (t * X ω)) μ) :
  (μ {ω | ε ≤ X ω}).to_real ≤ real.exp(- t * ε + cgf X μ t) :=
begin
  refine (measure_ge_le_exp_mul_mgf ε ht h_int).trans _,
  rw real.exp_add,
  exact mul_le_mul le_rfl (real.le_exp_log _) mgf_nonneg (real.exp_pos _).le,
end

/-- **Chernoff bound** on the lower tail of a real random variable. -/
lemma measure_le_le_exp_cgf [is_finite_measure μ] (ε : ℝ) (ht : t ≤ 0)
  (h_int : integrable (λ ω, real.exp (t * X ω)) μ) :
  (μ {ω | X ω ≤ ε}).to_real ≤ real.exp(- t * ε + cgf X μ t) :=
begin
  refine (measure_le_le_exp_mul_mgf ε ht h_int).trans _,
  rw real.exp_add,
  exact mul_le_mul le_rfl (real.le_exp_log _) mgf_nonneg (real.exp_pos _).le,
end

end moment_generating_function

end probability_theory
