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

Let `ℙ` be a probability measure, and let `Za i` and `Zb i` for $$i ∈ {1, 2, 3}$$ be random
variables taking values in $${-1, 1}$$. For convenience, we identify $${-1, 1}$$ with `ℤˣ`. `Za i`
represent the outcomes of measurements done by $$A$$, and `Zb i` those done by $$B$$. We assume
perfect anticorrelation between the outcomes of $$A$$ and $$B$$: 𝔼[(Za i) (Zb i)] = -1. Bell's
inequality states that `𝔼[(Za 1) (Zb 2)] - 𝔼[(Za 1) (Zb 2)] ≤ 1 + 𝔼[(Za 2) (Zb 3)]`.

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
``
-/

section
variables {α β : Type*} [measurable_space α] [measurable_space β] [measurable_singleton_class β]
  {f : α → β} [finite β]
open measure_theory

@[simps] def simple_func.of_finite (hf : measurable f) : simple_func α β :=
{ to_fun := f,
  measurable_set_fiber' := λ x, hf $ measurable_set_singleton _,
  finite_range' := (set.range f).to_finite}

end

section
variables {α β : Type*} [measurable_space α] [measurable_space β] [topological_space β]
  [measurable_singleton_class β] [finite β] {f : α → β}
open measure_theory

lemma measurable.strongly_measurable_of_finite (hf : measurable f) : strongly_measurable f :=
⟨λ n, simple_func.of_finite hf, λ a, tendsto_const_nhds⟩

end

noncomputable theory

open filter measure_theory

section preliminaries
variables {Ω : Type*} [measurable_space Ω] {ℙ : measure Ω} [is_finite_measure ℙ] {f : Ω → ℤˣ}

private lemma pm_one_space_abs_le (a : ℤˣ) : ‖(a : ℝ)‖ ≤ 1 :=
by obtain rfl | rfl := int.units_eq_one_or a; simp

/-- The CHSH inequality in `ℤˣ`. -/
lemma CHSH_inequality_of_int_units (A₀ A₁ B₀ B₁ : ℤˣ) :
  (A₀ : ℝ) * B₀ + A₀ * B₁ + A₁ * B₀ + (-A₁) * B₁ + -2 ≤ 0 :=
  by obtain rfl | rfl := int.units_eq_one_or A₀; obtain rfl | rfl := int.units_eq_one_or A₁;
    obtain rfl | rfl := int.units_eq_one_or B₀; obtain rfl | rfl := int.units_eq_one_or B₁; norm_num

private lemma integrable_aux (hf : measurable f) : integrable (λ ω, (f ω : ℝ)) ℙ :=
begin
  refine ⟨(measurable.comp (λ s hs, _) hf).ae_strongly_measurable, has_finite_integral_of_bounded $
    eventually_of_forall $ λ _, pm_one_space_abs_le _⟩,
  exact ⟨coe ⁻¹' s, trivial, rfl⟩,
end

end preliminaries

section bell_inequality_1964
variables {Ω : Type*} [measurable_space Ω] {ℙ : measure Ω} [is_finite_measure ℙ] {Za Zb : Ω → ℤˣ}

/-- **Bell's inequality (1964 version)** Given six random variables `Za Zb : fin 3 → Ω → ℤˣ` taking
values in `±1`, and assuming perfect anticorrelation on the diagonal (that is,
`𝔼[(Za i) (Zb i)] = -1` for all `i`), we have that
`𝔼[(Za 1) (Zb 2)] - 𝔼[(Za 1) (Zb 2)] ≤ 1 + 𝔼[(Za 2) (Zb 3)]`. -/
theorem bell_inequality_1964 (hℙ : is_probability_measure ℙ) {Za Zb : fin 3 → Ω → ℤˣ}
  (ha : ∀ i, measurable (Za i)) (hb : ∀ i, measurable (Zb i))
  (anticorrelation : ∀ i, ∫ ω, (Za i ω * Zb i ω : ℝ) ∂ℙ = -1) :
  ∫ ω, (Za 1 ω * Zb 2 ω : ℝ) ∂ℙ - ∫ ω, Za 1 ω * Zb 3 ω ∂ℙ ≤ 1 + ∫ ω, Za 2 ω * Zb 3 ω ∂ℙ :=
begin
  -- let integrable_muls :=
  --   λ i j, integrable_mul_of_units_int (Za_measurable i) (Zb_measurable j),
  -- let integrable_mul_negs :=
  --   λ i j, integrable_mul_of_units_int_neg (Za_measurable i) (Zb_measurable j),
  rw [←sub_nonpos, sub_add_eq_sub_sub, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg],
  have : ∀ ω,
    (-Za 2 ω : ℝ) * Zb 2 ω + -Za 2 ω * Zb 3 ω + Za 1 ω * Zb 2 ω + -Za 1 ω * Zb 3 ω + -2 ≤ 0,
  { intro ω,
    convert CHSH_inequality_of_int_units (-(Za 2 ω)) (Za 1 ω) (Zb 2 ω) (Zb 3 ω);
    simp },
  have int_chsh := @integral_nonpos _ _ ℙ _ (λ x, this x),
  rw [integral_add, integral_add, integral_add, integral_add] at int_chsh,
    try { apply_rules [integrable_const, integrable_muls, integrable_mul_negs, integrable.add] },
  sorry { have : ∫ ω, -(Za 2 ω : ℝ) * (Zb 2 ω) ∂ℙ = 1,
    { convert neg_inj.mpr (anticorrelation 2),
      { rw ← measure_theory.integral_neg,
        rw integral_congr_ae,
        filter_upwards with x,
        simp },
      { simp } },
    rw [this, (by simp : ∫ ω, (-2 : ℝ) ∂ℙ = -2)] at int_chsh,
    convert int_chsh using 1,
    ring_nf,
    congr' 1,
    rw [add_sub_left_comm, integral_neg, integral_neg],
    congr' 3,
    { ext1 x,
      ring },
    { congrm ∫ x, _,
      ring } },
  simp only [coe_coe],
  norm_cast,
  exact integrable_aux ((ha _).neg.mul $ hb _),

end

end bell_inequality_1964
