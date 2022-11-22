/-
Copyright (c) 2022 Ian Jauslin and Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Jauslin, Alex Kontorovich
-/

import measure_theory.measure.probability_measure
import probability.conditional_probability

/-!
# Bell's Inequality

This file proves Bell's Inequality as a probabilistic statement in several
forms. (TODO: Add other forms.)

A star-algebra version of Bell's inequality has already been proved in
  `algebra.star.chsh.CHSH_inequality_of_comm`
Here, the inequality is formulated in terms of probabilities.

Bell's inequality is the cornerstone of Bell's theorem, which states that
quantum mechanics is a non-local theory. The proof of Bell's theorem,
established by J.S. Bell in 1964, first uses the Einstein-Podolsky-Rosen
argument to establish that either quantum mechanics is non-local, or all
quantum observables simultaneously have values (in other words, quantum
mechanics is a non-contextual hidden variable theory). Bell's inequality is a
necessary condition for all the observables in an abstract probabilistic theory
to simultaneously have values. By showing that, in quantum mechanics, Bell's
inequality is violated, Bell proved that quantum mechanics is non-local.

The violation of Bell's inequality has also been verified experimentally in
many different setups.


## Bell's 1964 inequality

We first prove Bell's original statement of the inequality, which was published
in 1964, and will thus be called `bells_inequality_1964` in this file.

Consider two observers, A and B, performing measurements that take values in
{-1,+1}.

Let `ℙ` be a probability measure, and let `Za i` and `Zb i` for i∈{1,2,3} be
random variables taking values in {-1,+1}. For convenience, we identify {-1,+1}
with ℤˣ. `Za i` represent the outcomes of measurements done by A, and `Zb i`
those done by B. We assume perfect anticorrelation between the outcomes of A
and B: 𝔼[(Za i) (Zb i)] = -1. Bell's inequality states that
  `𝔼[(Za 1) (Zb 2)] - 𝔼[(Za 1) (Zb 2)] ≤ 1 + 𝔼[(Za 2) (Zb 3)]`.


## Future work

J.S. Bell generalized the inequality in 1975 to include more probabilistic
theories. In particular, the 1975 statement does not require observables to
simultaneously have values. Instead, it is solely based on the requirement of
locality. The 1975 inequality thus gives a more direct proof of Bell's theorem.


## References

* [J.S. Bell, *On the Einstein Podolsky Rosen Paradox*, 1964][MR3790629]

* [J.S. Bell, *The theory of local beables*, 1975,
  reproduced in chapter 7 of *Speakable and unspeakable in quantum mechanics*][MR915338]

-/

noncomputable theory

open measure_theory

section preliminaries_1964

lemma pm_one_space_vals (r : ℤˣ) :
  (r : ℝ) = 1 ∨ (r : ℝ) = -1 := by cases int.units_eq_one_or r with hh hh; rw hh; simp

lemma pm_one_space_abs_le (r : ℤˣ) :
  |(r : ℝ)| ≤ 1 := by cases int.units_eq_one_or r with hh hh; rw hh; simp

/-- The CHSH inequality in `ℤˣ`. -/
lemma CHSH_inequality_of_int_units (A₀ A₁ B₀ B₁ : ℤˣ) :
  (A₀ : ℝ) * B₀ + A₀ * B₁ + A₁ * B₀ + (-A₁) * B₁ + -2 ≤ 0 :=
  by cases pm_one_space_vals A₀ with hA0 hA0; cases pm_one_space_vals A₁ with hA1 hA1;
    cases pm_one_space_vals B₀ with hB0 hB0; cases pm_one_space_vals B₁ with hB1 hB1;
    rw [hA0, hA1, hB0, hB1]; ring_nf; simp

end preliminaries_1964

section bell_1964

variables {Ω : Type*} [measurable_space Ω] {ℙ : measure Ω}

lemma integrable_mul_of_units_int (hℙ : is_probability_measure ℙ) {Za Zb : Ω → ℤˣ}
  (sm_a : strongly_measurable (λ ω, (Za ω : ℝ))) (sm_b : strongly_measurable (λ ω, (Zb ω : ℝ))) :
  integrable (λ ω, (Za ω : ℝ) * Zb ω) ℙ :=
begin
  refine ⟨strongly_measurable.ae_strongly_measurable (strongly_measurable.mul sm_a sm_b), _⟩,
  refine @has_finite_integral_of_bounded _ _ _ _ _ _ _ (1 : ℝ) _,
  filter_upwards with x,
  convert pm_one_space_abs_le (Za x * Zb x),
  simp,
end

lemma integrable_mul_of_units_int_neg (hℙ : is_probability_measure ℙ) {Za Zb : Ω → ℤˣ}
  (sm_a : strongly_measurable (λ ω, (Za ω : ℝ))) (sm_b : strongly_measurable (λ ω, (Zb ω : ℝ))) :
  integrable (λ ω : Ω , -(Za ω :ℝ) * Zb ω) ℙ :=
begin
  convert @integrable_mul_of_units_int _ _ _ hℙ (λ x, -Za x) Zb _ sm_b,
  { ext1 x,
    simp, },
 { convert strongly_measurable.neg sm_a,
   ext1 x,
   simp, },
end

/-- **Bell's inequality (1964 version)** Given six random variables `Za Zb : fin 3 → Ω → ℤˣ` taking
  values in `±1`, and assuming perfect anticorrelation on the diagonal (that is,
  `𝔼[(Za i) (Zb i)] = -1` for all `i`), we have that
  `𝔼[(Za 1) (Zb 2)] - 𝔼[(Za 1) (Zb 2)] ≤ 1 + 𝔼[(Za 2) (Zb 3)]`. -/
theorem bells_inequality_1964 (hℙ : is_probability_measure ℙ) {Za Zb : fin 3 → Ω → ℤˣ}
  (Za_measurable : ∀ i, strongly_measurable (λ ω, (Za i ω : ℝ)))
  (Zb_measurable : ∀ i, strongly_measurable (λ ω, (Zb i ω : ℝ)))
  (anticorrelation : ∀ i, ∫ ω, (Za i ω : ℝ) * (Zb i ω) ∂ℙ = -1) :
  (∫ ω, (Za 1 ω : ℝ) * (Zb 2 ω) ∂ℙ) - (∫ ω, (Za 1 ω : ℝ) * (Zb 3 ω) ∂ℙ)
    ≤ 1 + (∫ ω, (Za 2 ω : ℝ) * (Zb 3 ω) ∂ℙ) :=
begin
  let integrable_muls :=
    λ i j, integrable_mul_of_units_int hℙ (Za_measurable i) (Zb_measurable j),
  let integrable_mul_negs :=
    λ i j, integrable_mul_of_units_int_neg hℙ (Za_measurable i) (Zb_measurable j),
  rw sub_eq_add_neg,
  apply sub_nonpos.mp,
  rw [sub_add_eq_sub_sub, sub_eq_add_neg, sub_eq_add_neg],
  have : ∀ ω, (-Za 2 ω : ℝ) * (Zb 2 ω) + (-Za 2 ω) * (Zb 3 ω) + (Za 1 ω) * (Zb 2 ω)
                  + -(Za 1 ω) * (Zb 3 ω) + -2 ≤ 0 ,
  { intro ω,
    convert CHSH_inequality_of_int_units (-(Za 2 ω)) (Za 1 ω) (Zb 2 ω) (Zb 3 ω);
    simp, },
  have int_chsh := @integral_nonpos _ _ ℙ _ (λ x, this x),
  rw [integral_add, integral_add, integral_add, integral_add] at int_chsh,
  { have : ∫ ω, -(Za 2 ω : ℝ) * (Zb 2 ω) ∂ℙ = 1,
    { convert neg_inj.mpr (anticorrelation 2),
      { rw ← measure_theory.integral_neg,
        rw integral_congr_ae,
        filter_upwards with x,
        simp, },
      { simp, }, },
    rw [this, (by simp : ∫ ω, (-2 : ℝ) ∂ℙ = -2)] at int_chsh,
    convert int_chsh using 1,
    ring_nf,
    congr' 1,
    rw add_sub_left_comm,
    congr' 1,
    { rw integral_neg,
      congr' 2,
      ext1 x,
      ring, },
    { congr' 1,
      rw integral_neg,
      congr' 2,
      ext1 x,
      ring, }, },
  { exact integrable_mul_negs 2 2, },
  { exact integrable_mul_negs 2 3, },
  { exact integrable.add (integrable_mul_negs 2 2) (integrable_mul_negs 2 3), },
  { exact integrable_muls 1 2, },
  { refine integrable.add (integrable.add (integrable_mul_negs 2 2) (integrable_mul_negs 2 3)) _,
    exact integrable_muls 1 2, },
  { exact integrable_mul_negs 1 3, },
  { refine integrable.add _ (integrable_mul_negs 1 3),
    refine integrable.add _ (integrable_muls 1 2),
    exact integrable.add (integrable_mul_negs 2 2) (integrable_mul_negs 2 3), },
  { apply integrable_const, },
  { exact has_add.to_covariant_class_right ℝ, },
end

end bell_1964


section bell_1975

variables {Ω : Type*} [measurable_space Ω]

-- Bell's inequality: 1975 version
theorem bells_inequality_1975
  -- parameter space for experiments
  {Aa Ab : Type*}
  -- shared variable space
  {Λ : Type*}
  [measure_space Λ]
  [topological_space Λ]

  -- random variables
  (Xa : Ω → (set.interval (-1:ℝ) 1))
  (Xb : Ω → (set.interval (-1:ℝ) 1))
  (Xa_measurable : strongly_measurable (λ ω, (Xa ω : ℝ)))
  (Xb_measurable : strongly_measurable (λ ω, (Xb ω : ℝ)))

  -- probability distribution on outcomes of experiments that depends on two parameters α∈Aa and β∈Ab
  (ℙab : Aa → Ab → (measure Ω))
  -- factorized probabilities
  (ℙa : Aa → (measure Ω))
  (ℙb : Ab → (measure Ω))

  -- shared variable
  (lam : Ω → Λ)
  (lam_measurable : strongly_measurable lam)
  -- probability distribution on shared variable
  (P_lam : measure Ω)
  (hP_lam : is_probability_measure P_lam)

  -- locality assumption
  (locality : ∀ l:Λ, ∀ α:Aa, ∀ β:Ab ,
    ∫ ω , (Xa ω :ℝ) * (Xb ω) ∂(probability_theory.cond (ℙab α β) (lam ⁻¹' {l})) =
      ∫ ω , (Xa ω :ℝ) * (Xb ω) ∂(probability_theory.cond (ℙa α) (lam ⁻¹' {l})) *
      ∫ ω , (Xa ω :ℝ) * (Xb ω) ∂(probability_theory.cond (ℙb β) (lam ⁻¹' {l})) )
  :
  ∀ α : Aa , ∀ α' : Aa, ∀ β : Ab , ∀ β' : Ab ,
  | (∫ ω, (Xa ω : ℝ) * (Xb ω) ∂(ℙab α β) )
    - (∫ ω, (Xa ω : ℝ) * (Xb ω) ∂(ℙab α β') ) |
  + | (∫ ω, (Xa ω : ℝ) * (Xb ω) ∂(ℙab α' β) )
    - (∫ ω, (Xa ω : ℝ) * (Xb ω) ∂(ℙab α' β') ) |
    ≤ 2
  :=

begin
  intros α α' β β',
  
  let ℙab_cond:= λ α β l , (probability_theory.cond ((ℙab α β):measure Ω) (lam ⁻¹' {l})),
  
  have cond_expectation :
  ∫ ω, (Xa ω : ℝ) * (Xb ω) ∂((ℙab α β):measure Ω)
    = ∫ l:Λ, ∫ ω , (Xa ω : ℝ) * (Xb ω) ∂(ℙab_cond α β l),


  sorry,
  sorry,
end

end bell_1975
