/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.moments

/-! # Sub-Gaussian random variables

This presentation of sub-Gaussian random variables is inspired by section 2.5 of
[vershynin2018high]. Let `X` be a random variable. We define the following five properties, where
`Kᵢ` are positive reals,
* (i) for all `t ≥ 0`, `ℙ(|X| ≥ t) ≤ 2 * exp(-t^2 / K₁^2)`,
* (ii) for all `p : ℕ` with `1 ≤ p`, `𝔼[|X|^p]^(1/p) ≤ K₂ sqrt(p)`,
* (iii) for all `|t| ≤ 1/K₃`, `𝔼[exp(t^2 * X^2)] ≤ exp(K₃^2 * t^2)`,
* (iv) `𝔼[exp(X^2 / K₄)] ≤ 2`,
* (v) for all `t : ℝ`, `log 𝔼[exp(t*X)] ≤ K₅ t^2 / 2`.

Properties (i) to (iv) are equivalent, in the sense that there exists a constant `C` such that
if `X` verifies one of those properties with constant `K`, then it verifies any other one with
constant at most `CK`.

If `𝔼[X] = 0` then properties (i)-(iv) are equivalent to (v) in that same sense.

The name sub-Gaussian is used by various authors to refer to any one of (i)-(v). We will say that a
random variable has sub-Gaussian cumulant generating function (cgf) with constant `K₅` to mean that
property (v) holds with that constant. The function `t^2 / 2` which appears in property (v) is the
cgf of a Gaussian with variance 1.

TODO: implement (i)-(iv) and prove relations between those properties.

## Main definitions

* `subgaussian_cgf X μ c`: the random variable `X` has a sub-Gaussian cgf, with constant `c`. That
  is, for all `t ∈ ℝ` `exp(t*X)` is integrable (the cgf is well defined) and
  `cgf X μ t ≤ c * t^2 / 2`.

## Main statements

* `Indep_fun.prob_sum_range_ge_le_of_subgaussian_cgf`: For `X : ℕ → Ω → ℝ` an independent family of
  real random variables, all with sub-Gaussian cdf with constant `c`, we have for all `ε ≥ 0`,
  `ℙ(ε ≤ ∑ i in finset.range n, X i) ≤ exp(- ε^2 / (2 * c * n))`. This is **Hoeffding's inequality**
  for sub-Gaussian random variables.

## References

* [R. Vershynin, *High-dimensional probability: An introduction with applications in data
science*][vershynin2018high]

-/


open measure_theory filter finset real

noncomputable theory

open_locale big_operators measure_theory probability_theory ennreal nnreal

namespace probability_theory

variables {Ω : Type*} {m : measurable_space Ω} {X : Ω → ℝ} {μ : measure Ω} {t c ε : ℝ}

include m

/-- A random variable has a sub-Gaussian cumulant generating function if this function is defined
on `ℝ` and verifies `cgf X μ t ≤ c * t^2 / 2` for some real `c` and all `t ∈ ℝ`. -/
def subgaussian_cgf (X : Ω → ℝ) (μ : measure Ω) (c : ℝ) : Prop :=
∀ t, integrable (λ ω, exp (t * X ω)) μ ∧ cgf X μ t ≤ c * t^2 / 2

lemma subgaussian_cgf.cgf_le (h : subgaussian_cgf X μ c) (t : ℝ) : cgf X μ t ≤ c * t^2 / 2 :=
(h t).2

lemma subgaussian_cgf.integrable_exp_mul (h : subgaussian_cgf X μ c) (t : ℝ) :
  integrable (λ ω, exp (t * X ω)) μ := (h t).1

lemma subgaussian_cgf.mgf_le (h : subgaussian_cgf X μ c) (t : ℝ) :
  mgf X μ t ≤ exp (c * t^2 / 2) :=
calc mgf X μ t ≤ exp (cgf X μ t) : le_exp_log _
... ≤ exp (c * t^2 / 2) : exp_monotone (h.cgf_le t)

lemma subgaussian_cgf_zero [is_probability_measure μ] (hc : 0 ≤ c) : subgaussian_cgf 0 μ c :=
begin
  refine λ t, ⟨_, _⟩,
  { simp only [pi.zero_apply, mul_zero, exp_zero],
    exact integrable_const _, },
  { simp only [cgf_zero_fun, measure_univ, ennreal.one_to_real, log_one],
    exact div_nonneg (mul_nonneg hc (sq_nonneg _)) zero_le_two, },
end

lemma subgaussian_cgf.neg (h : subgaussian_cgf X μ c) :
  subgaussian_cgf (-X) μ c :=
begin
  refine λ t, ⟨_, _⟩,
  { simp_rw [pi.neg_apply, mul_neg, ← neg_mul],
    exact (h (-t)).1, },
  { rw cgf_neg,
    refine (h.cgf_le (-t)).trans _,
    rw neg_pow_two, },
end

lemma subgaussian_cgf.add_indep_fun {Y : Ω → ℝ} {cX cY : ℝ} (hX : subgaussian_cgf X μ cX)
  (hY : subgaussian_cgf Y μ cY) (hindep : indep_fun X Y μ) :
  subgaussian_cgf (X + Y) μ (cX + cY) :=
begin
  intros t,
  refine ⟨hindep.integrable_exp_mul_add (hX.integrable_exp_mul t) (hY.integrable_exp_mul t), _⟩,
  rw hindep.cgf_add (hX.integrable_exp_mul t) (hY.integrable_exp_mul t),
  calc cgf X μ t + cgf Y μ t
      ≤ cX * t ^ 2 / 2 + cY * t ^ 2 / 2 : add_le_add (hX.cgf_le t) (hY.cgf_le t)
  ... = (cX + cY) * t ^ 2 / 2 : by ring,
end

lemma Indep_fun.subgaussian_cgf_sum {ι : Type*} [is_probability_measure μ]
  {X : ι → Ω → ℝ} (h_indep : Indep_fun (λ i, infer_instance) X μ) {c : ι → ℝ}
  (h_meas : ∀ i, measurable (X i))
  {s : finset ι} (h_subg : ∀ i ∈ s, subgaussian_cgf (X i) μ (c i)) :
  subgaussian_cgf (∑ i in s, X i) μ (∑ i in s, c i) :=
begin
  intros t,
  refine ⟨h_indep.integrable_exp_mul_sum h_meas (λ i hi, (h_subg i hi).integrable_exp_mul t), _⟩,
  rw [h_indep.cgf_sum h_meas (λ i hi, (h_subg i hi).integrable_exp_mul t), sum_mul, sum_div],
  exact sum_le_sum (λ i hi, (h_subg i hi).cgf_le t),
end

lemma subgaussian_cgf.measure_ge_le [is_finite_measure μ]
  (h : subgaussian_cgf X μ c) (hc : 0 < c) (hε : 0 ≤ ε) :
  (μ {ω | ε ≤ X ω}).to_real ≤ exp (- ε^2 / (2*c)) :=
begin
  have h_le_t : ∀ t : ℝ, 0 ≤ t → (μ {ω | ε ≤ X ω}).to_real ≤ exp (- t * ε + c * t^2 / 2),
  { refine λ t ht, (measure_ge_le_exp_cgf ε ht (h.integrable_exp_mul t)).trans _,
    exact exp_monotone (add_le_add le_rfl (h.cgf_le t)), },
  refine (h_le_t (ε / c) (div_nonneg hε hc.le)).trans_eq _,
  congr,
  rw [div_pow, pow_two c, mul_div, mul_div_mul_comm, div_self hc.ne', one_mul, neg_mul,
    div_mul_eq_mul_div, ← pow_two, mul_comm, ← div_div],
  ring,
end

lemma subgaussian_cgf.prob_ge_le [is_probability_measure μ]
  (h : subgaussian_cgf X μ c) (hε : 0 ≤ ε) :
  (μ {ω | ε ≤ X ω}).to_real ≤ exp (- ε^2 / (2*c)) :=
begin
  cases lt_or_le 0 c with hc hc,
  { exact h.measure_ge_le hc hε, },
  suffices : 1 ≤ exp (-ε ^ 2 / (2 * c)), from to_real_prob_le_one.trans this,
  rw one_le_exp_iff,
  exact div_nonneg_of_nonpos (neg_nonpos_of_nonneg (sq_nonneg _))
    (mul_nonpos_of_nonneg_of_nonpos zero_le_two hc),
end

section sums

variables {ι : Type*} [is_probability_measure μ] {Xs : ι → Ω → ℝ}

/-- **Hoeffding's inequality** for independent sub-Gaussian random variables. -/
lemma Indep_fun.prob_sum_ge_le_of_subgaussian_cgf'
  (h_indep : Indep_fun (λ i, infer_instance) Xs μ) {c : ι → ℝ}
  (h_meas : ∀ i, measurable (Xs i))
  {s : finset ι} (h_subg : ∀ i ∈ s, subgaussian_cgf (Xs i) μ (c i)) (hε : 0 ≤ ε) :
  (μ {ω | ε ≤ ∑ i in s, Xs i ω}).to_real ≤ exp (- ε^2 / (2 * (∑ i in s, c i))) :=
begin
  simp_rw ← finset.sum_apply,
  exact (h_indep.subgaussian_cgf_sum h_meas h_subg).prob_ge_le hε,
end

/-- **Hoeffding's inequality** for independent sub-Gaussian random variables. -/
lemma Indep_fun.prob_sum_ge_le_of_subgaussian_cgf
  (h_indep : Indep_fun (λ i, infer_instance) Xs μ) (h_meas : ∀ i, measurable (Xs i))
  {s : finset ι} (h_subg : ∀ i ∈ s, subgaussian_cgf (Xs i) μ c) (hε : 0 ≤ ε) :
  (μ {ω | ε ≤ ∑ i in s, Xs i ω}).to_real ≤ exp (- ε^2 / (2 * c * (card s))) :=
calc (μ {ω | ε ≤ ∑ i in s, Xs i ω}).to_real
    ≤ exp (- ε^2 / (2 * (∑ i in s, c))) :
      h_indep.prob_sum_ge_le_of_subgaussian_cgf' h_meas h_subg hε
... = exp (- ε^2 / (2 * c * (card s))) :
    by { rw mul_assoc, congr, rw [sum_const, nsmul_eq_mul, mul_comm c], }

/-- **Hoeffding's inequality** for independent sub-Gaussian random variables. -/
lemma Indep_fun.prob_sum_range_ge_le_of_subgaussian_cgf {X : ℕ → Ω → ℝ}
  (h_indep : Indep_fun (λ i, infer_instance) X μ) (h_meas : ∀ i, measurable (X i))
  (h_subg : ∀ i, subgaussian_cgf (X i) μ c) (hε : 0 ≤ ε) (n : ℕ) :
  (μ {ω | ε ≤ ∑ i in finset.range n, X i ω}).to_real ≤ exp (- ε^2 / (2 * c * n)) :=
begin
  cases n,
  { simp only [range_zero, sum_empty, nat.cast_zero, mul_zero, div_zero, exp_zero],
    exact to_real_prob_le_one, },
  calc (μ {ω | ε ≤ ∑ i in finset.range n.succ, X i ω}).to_real
      ≤ exp (- ε^2 / (2 * c * (card (finset.range n.succ)))) :
        h_indep.prob_sum_ge_le_of_subgaussian_cgf h_meas (λ i _, h_subg i) hε
  ... = exp (- ε^2 / (2 * c * n.succ)) : by rw card_range
end

/-- **Hoeffding's inequality** for independent sub-Gaussian random variables. -/
lemma Indep_fun.prob_mean_range_ge_le_of_subgaussian_cgf {X : ℕ → Ω → ℝ}
  (h_indep : Indep_fun (λ i, infer_instance) X μ) (h_meas : ∀ i, measurable (X i))
  (h_subg : ∀ i, subgaussian_cgf (X i) μ c) (hε : 0 ≤ ε) (n : ℕ) :
  (μ {ω | ε ≤ (∑ i in finset.range n, X i ω) / n}).to_real ≤ exp (- n * ε^2 / (2 * c)) :=
begin
  cases n,
  { simp only [range_zero, sum_empty, nat.cast_zero, neg_zero', zero_mul, zero_div, exp_zero],
    exact to_real_prob_le_one, },
  have h_nε : 0 ≤ ↑n.succ * ε := mul_nonneg (nat.cast_nonneg _) hε,
  have h := h_indep.prob_sum_range_ge_le_of_subgaussian_cgf h_meas h_subg h_nε n.succ,
  refine (eq.trans_le _ (h.trans_eq _)),
  { congr' with ω,
    rw [le_div_iff (nat.cast_pos.mpr n.succ_pos), mul_comm ε],
    apply_instance, },
  { congr' 1,
    by_cases hc : c = 0,
    { simp only [hc, mul_zero, zero_mul, div_zero], },
    field_simp [n.cast_add_one_ne_zero],
    ring, },
end

end sums

end probability_theory
