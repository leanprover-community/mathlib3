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

Consider two observers, $$A$$ and $$B$$, performing three measurements that take values in
$${-1, 1}$$. Assuming perfect anticorrelation of their measurements, we can represent the outcomes
by $$a, b, c$$ (for $$A$$) and $$-a, -b, -c$$ (for $$B$$). Bell's inequality states that
$$|𝔼[a * -b] - 𝔼[a * -c]| ≤ 1 + 𝔼[b * -c]$$.

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

namespace bell_inequality
variables {Ω : Type*} [measurable_space Ω] {ℙ : measure Ω} [is_probability_measure ℙ] {f g : Ω → ℤˣ}
  {a b c : Ω → ℤˣ}

private lemma norm_aux (a : ℤˣ) : ‖(a : ℝ)‖ ≤ 1 :=
by obtain rfl | rfl := int.units_eq_one_or a; simp

/-- The precise version of the CHSH inequality we need. -/
private lemma CHSH_aux (a b c : ℤˣ) : (a : ℝ) * -b - a * -c ≤ 1 + b * -c :=
by obtain rfl | rfl := int.units_eq_one_or a; obtain rfl | rfl := int.units_eq_one_or b;
  obtain rfl | rfl := int.units_eq_one_or c; norm_num

private lemma ae_strongly_measurable_aux (hf : ae_measurable f ℙ) :
  ae_strongly_measurable (λ ω, (f ω : ℝ)) ℙ :=
begin
  refine (measurable.comp_ae_measurable (λ s hs, _) hf).ae_strongly_measurable,
  exact ⟨coe ⁻¹' s, trivial, rfl⟩,
end

private lemma integrable_aux (hf : ae_measurable f ℙ) : integrable (λ ω, (f ω : ℝ)) ℙ :=
⟨ae_strongly_measurable_aux hf, has_finite_integral_of_bounded $ eventually_of_forall $ λ _,
  norm_aux _⟩

private lemma integrable_mul_aux (hf : ae_measurable f ℙ) (hg : ae_measurable g ℙ) :
  integrable (λ ω, (f ω * g ω : ℝ)) ℙ :=
(integrable_aux hg).bdd_mul (ae_strongly_measurable_aux hf) ⟨1, λ _, norm_aux _⟩

/-- Given three random variables `a b c` taking values in `±1`, we have that
`𝔼[a * -b] - 𝔼[a * -c] ≤ 1 + 𝔼[b * -c]`. -/
private lemma bell_aux (ha : ae_measurable a ℙ) (hb : ae_measurable b ℙ) (hc : ae_measurable c ℙ) :
  (∫ ω, a ω * -b ω ∂ℙ : ℝ) - ∫ ω, a ω * -c ω ∂ℙ ≤ 1 + ∫ ω, b ω * -c ω ∂ℙ :=
begin
  have integral_one : ∫ ω, (1 : ℝ) ∂ℙ = 1, by simp,
  have anticorrelation : (∫ ω, c ω * c ω ∂ℙ : ℝ) = 1, by simp [←units.coe_mul, ←int.cast_mul],
  rw [←integral_one, ←integral_sub, ←integral_add],
  refine integral_mono _ _ (λ _, CHSH_aux _ _ _),
  all_goals -- discharge all the integrability hypotheses
  { try { simp only [coe_coe, ←int.cast_neg, ←units.coe_neg] },
    apply_rules [integrable.add, integrable.neg, integrable_mul_aux, integrable_const,
      ae_measurable.neg, ha, hb, hc] },
end

/-- **Bell's inequality (1964 version)**. Given three random variables `a b c` taking values in
`±1`, we have that `|𝔼[a * -b] - 𝔼[a * -c]| ≤ 1 + 𝔼[b * -c]`. -/
theorem bell_inequality_1964 (ha : ae_measurable a ℙ) (hb : ae_measurable b ℙ)
  (hc : ae_measurable c ℙ) :
  |(∫ ω, a ω * -b ω ∂ℙ - ∫ ω, a ω * -c ω ∂ℙ : ℝ)| ≤ 1 + ∫ ω, b ω * -c ω ∂ℙ :=
abs_sub_le_iff.2 ⟨bell_aux ha hb hc, (bell_aux ha hc hb).trans_eq $ by simp_rw [mul_neg, mul_comm]⟩

end bell_inequality
