/-
Copyright (c) 2022 Ian Jauslin and Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Jauslin, Alex Kontorovich
-/
import measure_theory.measure.probability_measure

/-!
# Bell's Inequality

This file proves Bell's Inequality as a probabilistic statement in several forms.

Bell's inequality is the cornerstone of Bell's theorem, which states that quantum mechanics is a
non-local theory. The proof of Bell's theorem, established by J.S. Bell in 1964, first uses the
Einstein-Podolsky-Rosen argument to establish that either quantum mechanics is non-local, or all
quantum observables simultaneously have values (in other words, quantum mechanics is a
non-contextual hidden variable theory). Bell's inequality is a necessary condition for all the
observables in an abstract probabilistic theory to simultaneously have values. By showing that, in
quantum mechanics, Bell's inequality is violated, Bell proved that quantum mechanics is non-local.

The violation of Bell's inequality has also been verified experimentally in many different setups.

## Bell's 1964 inequality

We first prove Bell's original statement of the inequality, which was published in 1964, and will
thus be called `bell_inequality_1964` in this file.

Consider two observers, $$A$$ and $$B$$, performing measurements that take values in $${-1, 1}$$.

Let `ℙ` be a probability measure, and let `A i` and `B i` for $$i ∈ {0, 1, 2}$$ be random
variables taking values in $${-1, 1}$$. For convenience, we identify $${-1, 1}$$ with `ℤˣ`. `A i`
represent the outcomes of measurements done by $$A$$, and `B i` those done by $$B$$. We assume
perfect anticorrelation between the outcomes of $$A$$ and $$B$$: 𝔼[(A i) (B i)] = -1. Bell's
inequality states that `𝔼[(A 1) (B 2)] - 𝔼[(A 1) (B 2)] ≤ 1 + 𝔼[(A 2) (B 0)]`.

## TODO

J.S. Bell generalized the inequality in 1975 to include more probabilistic theories. In particular,
the 1975 statement does not require observables to simultaneously have values. Instead, it is solely
based on the requirement of locality. The 1975 inequality thus gives a more direct proof of Bell's
theorem.

## References

* [J.S. Bell, *On the Einstein Podolsky Rosen Paradox*, 1964][MR3790629]
* [J.S. Bell, *The theory of local beables*, 1975,
  reproduced in chapter 7 of *Speakable and unspeakable in quantum mechanics*][MR915338]

## See also

`CHSH_inequality_of_comm` is a star-algebra version of Bell's inequality.
-/

open filter measure_theory

variables {Ω : Type*} [measurable_space Ω] {ℙ : measure Ω} [is_probability_measure ℙ] {f g : Ω → ℤˣ}
  {A B : fin 3 → Ω → ℤˣ}

private lemma norm_aux (a : ℤˣ) : ‖(a : ℝ)‖ ≤ 1 :=
by obtain rfl | rfl := int.units_eq_one_or a; simp

/-- The precise version of the CHSH inequality we need. -/
private lemma CHSH_aux (A₁ A₂ B₀ B₂ : ℤˣ) :
  (A₁ : ℝ) * B₂ - A₁ * B₀ - A₂ * B₂ ≤ 1 + A₂ * B₀ + 1 :=
by obtain rfl | rfl := int.units_eq_one_or A₁; obtain rfl | rfl := int.units_eq_one_or A₂;
  obtain rfl | rfl := int.units_eq_one_or B₀; obtain rfl | rfl := int.units_eq_one_or B₂; norm_num

private lemma ae_strongly_measurable_aux (hf : measurable f) :
  ae_strongly_measurable (λ ω, (f ω : ℝ)) ℙ :=
begin
  refine (measurable.comp (λ s hs, _) hf).ae_strongly_measurable,
  exact ⟨coe ⁻¹' s, trivial, rfl⟩,
end

private lemma integrable_aux (hf : measurable f) : integrable (λ ω, (f ω : ℝ)) ℙ :=
⟨ae_strongly_measurable_aux hf, has_finite_integral_of_bounded $ eventually_of_forall $ λ _,
  norm_aux _⟩

private lemma integrable_mul_aux (hf : measurable f) (hg : measurable g) :
  integrable (λ ω, (f ω * g ω : ℝ)) ℙ :=
(integrable_aux hg).bdd_mul (ae_strongly_measurable_aux hf) ⟨1, λ _, norm_aux _⟩

/-- **Bell's inequality (1964 version)** Given six random variables `A B : fin 3 → Ω → ℤˣ` taking
values in `±1`, and assuming perfect anticorrelation on the diagonal (that is, `𝔼[(A i) (B i)] = -1`
for all `i`), we have that `𝔼[(A 1) (B 2)] - 𝔼[(A 1) (B 0)] ≤ 1 + 𝔼[(A 2) (B 0)]`. -/
theorem bell_inequality_1964 (ha : ∀ i, measurable (A i)) (hb : ∀ i, measurable (B i))
  (anticorrelation : (∫ ω, A 2 ω * B 2 ω ∂ℙ : ℝ) = -1) :
  (∫ ω, A 1 ω * B 2 ω ∂ℙ : ℝ) - ∫ ω, A 1 ω * B 0 ω ∂ℙ ≤ 1 + ∫ ω, A 2 ω * B 0 ω ∂ℙ :=
begin
  rw [←sub_le_sub_iff_right (∫ ω, A 2 ω * B 2 ω ∂ℙ : ℝ), ←integral_sub, ←integral_sub,
    anticorrelation, sub_neg_eq_add, (by simp : (1 : ℝ) = ∫ ω, 1 ∂ℙ), ←integral_add, ←integral_add],
  refine integral_mono _ _ (λ _, CHSH_aux _ _ _ _),
  all_goals -- discharge all the integrability hypotheses
  { try { simp only [coe_coe, ←int.cast_neg, ←units.coe_neg] },
    apply_rules [integrable.add, integrable.neg, integrable_mul_aux, ha, hb, integrable_const] },
end
