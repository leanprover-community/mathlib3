/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.martingale.basic

/-!
# Centering lemma for stochastic processes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Any `ℕ`-indexed stochastic process which is adapted and integrable can be written as the sum of a
martingale and a predictable process. This result is also known as **Doob's decomposition theorem**.
From a process `f`, a filtration `ℱ` and a measure `μ`, we define two processes
`martingale_part f ℱ μ` and `predictable_part f ℱ μ`.

## Main definitions

* `measure_theory.predictable_part f ℱ μ`: a predictable process such that
  `f = predictable_part f ℱ μ + martingale_part f ℱ μ`
* `measure_theory.martingale_part f ℱ μ`: a martingale such that
  `f = predictable_part f ℱ μ + martingale_part f ℱ μ`

## Main statements

* `measure_theory.adapted_predictable_part`: `(λ n, predictable_part f ℱ μ (n+1))` is adapted. That
  is, `predictable_part` is predictable.
* `measure_theory.martingale_martingale_part`: `martingale_part f ℱ μ` is a martingale.

-/


open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators

namespace measure_theory

variables {Ω E : Type*} {m0 : measurable_space Ω} {μ : measure Ω}
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  {f : ℕ → Ω → E} {ℱ : filtration ℕ m0} {n : ℕ}

/-- Any `ℕ`-indexed stochastic process can be written as the sum of a martingale and a predictable
process. This is the predictable process. See `martingale_part` for the martingale. -/
noncomputable
def predictable_part {m0 : measurable_space Ω}
  (f : ℕ → Ω → E) (ℱ : filtration ℕ m0) (μ : measure Ω . volume_tac) : ℕ → Ω → E :=
λ n, ∑ i in finset.range n, μ[f (i+1) - f i | ℱ i]

@[simp] lemma predictable_part_zero : predictable_part f ℱ μ 0 = 0 :=
by simp_rw [predictable_part, finset.range_zero, finset.sum_empty]

lemma adapted_predictable_part : adapted ℱ (λ n, predictable_part f ℱ μ (n+1)) :=
λ n, finset.strongly_measurable_sum' _
  (λ i hin, strongly_measurable_condexp.mono (ℱ.mono (finset.mem_range_succ_iff.mp hin)))

lemma adapted_predictable_part' : adapted ℱ (λ n, predictable_part f ℱ μ n) :=
λ n, finset.strongly_measurable_sum' _
  (λ i hin, strongly_measurable_condexp.mono (ℱ.mono (finset.mem_range_le hin)))

/-- Any `ℕ`-indexed stochastic process can be written as the sum of a martingale and a predictable
process. This is the martingale. See `predictable_part` for the predictable process. -/
noncomputable
def martingale_part {m0 : measurable_space Ω}
  (f : ℕ → Ω → E) (ℱ : filtration ℕ m0) (μ : measure Ω . volume_tac) : ℕ → Ω → E :=
λ n, f n - predictable_part f ℱ μ n

lemma martingale_part_add_predictable_part (ℱ : filtration ℕ m0) (μ : measure Ω) (f : ℕ → Ω → E) :
  martingale_part f ℱ μ + predictable_part f ℱ μ = f :=
sub_add_cancel _ _

lemma martingale_part_eq_sum :
  martingale_part f ℱ μ =
    λ n, f 0 + ∑ i in finset.range n, (f (i+1) - f i - μ[f (i+1) - f i | ℱ i]) :=
begin
  rw [martingale_part, predictable_part],
  ext1 n,
  rw [finset.eq_sum_range_sub f n, ← add_sub, ← finset.sum_sub_distrib],
end

lemma adapted_martingale_part (hf : adapted ℱ f) :
  adapted ℱ (martingale_part f ℱ μ) :=
adapted.sub hf adapted_predictable_part'

lemma integrable_martingale_part (hf_int : ∀ n, integrable (f n) μ) (n : ℕ) :
  integrable (martingale_part f ℱ μ n) μ :=
begin
  rw martingale_part_eq_sum,
  exact (hf_int 0).add
    (integrable_finset_sum' _ (λ i hi, ((hf_int _).sub (hf_int _)).sub integrable_condexp)),
end

lemma martingale_martingale_part (hf : adapted ℱ f) (hf_int : ∀ n, integrable (f n) μ)
  [sigma_finite_filtration μ ℱ] :
  martingale (martingale_part f ℱ μ) ℱ μ :=
begin
  refine ⟨adapted_martingale_part hf, λ i j hij, _⟩,
  -- ⊢ μ[martingale_part f ℱ μ j | ℱ i] =ᵐ[μ] martingale_part f ℱ μ i
  have h_eq_sum : μ[martingale_part f ℱ μ j | ℱ i]
    =ᵐ[μ] f 0 + ∑ k in finset.range j, (μ[f (k+1) - f k | ℱ i] - μ[μ[f (k+1) - f k | ℱ k] | ℱ i]),
  { rw martingale_part_eq_sum,
    refine (condexp_add (hf_int 0) _).trans _,
    { exact integrable_finset_sum' _
        (λ i hij, ((hf_int _).sub (hf_int _)).sub integrable_condexp), },
    refine (eventually_eq.add eventually_eq.rfl (condexp_finset_sum (λ i hij, _))).trans _,
    { exact ((hf_int _).sub (hf_int _)).sub integrable_condexp, },
    refine eventually_eq.add _ _,
    { rw condexp_of_strongly_measurable (ℱ.le _) _ (hf_int 0),
      { apply_instance, },
      { exact (hf 0).mono (ℱ.mono (zero_le i)), }, },
    { exact eventually_eq_sum (λ k hkj, condexp_sub ((hf_int _).sub (hf_int _))
        integrable_condexp), }, },
  refine h_eq_sum.trans _,
  have h_ge : ∀ k, i ≤ k → μ[f (k + 1) - f k|ℱ i] - μ[μ[f (k + 1) - f k|ℱ k]|ℱ i] =ᵐ[μ] 0,
  { intros k hk,
    have : μ[μ[f (k + 1) - f k|ℱ k]|ℱ i] =ᵐ[μ] μ[f (k + 1) - f k|ℱ i],
    { exact condexp_condexp_of_le (ℱ.mono hk) (ℱ.le k), },
    filter_upwards [this] with x hx,
    rw [pi.sub_apply, pi.zero_apply, hx, sub_self], },
  have h_lt : ∀ k, k < i → μ[f (k + 1) - f k|ℱ i] - μ[μ[f (k + 1) - f k|ℱ k]|ℱ i]
    =ᵐ[μ] f (k + 1) - f k - μ[f (k + 1) - f k|ℱ k],
  { refine λ k hk, eventually_eq.sub _ _,
    { rw condexp_of_strongly_measurable,
      { exact ((hf (k+1)).mono (ℱ.mono (nat.succ_le_of_lt hk))).sub
          ((hf k).mono (ℱ.mono hk.le)), },
      { exact (hf_int _).sub (hf_int _), }, },
    { rw condexp_of_strongly_measurable,
      { exact strongly_measurable_condexp.mono (ℱ.mono hk.le), },
      { exact integrable_condexp, }, }, },
  rw martingale_part_eq_sum,
  refine eventually_eq.add eventually_eq.rfl _,
  rw [← finset.sum_range_add_sum_Ico _ hij,
    ← add_zero (∑ i in finset.range i, (f (i + 1) - f i - μ[f (i + 1) - f i | ℱ i]))],
  refine (eventually_eq_sum (λ k hk, h_lt k (finset.mem_range.mp hk))).add _,
  refine (eventually_eq_sum (λ k hk, h_ge k (finset.mem_Ico.mp hk).1)).trans _,
  simp only [finset.sum_const_zero, pi.zero_apply],
  refl,
end

-- The following two lemmas demonstrate the essential uniqueness of the decomposition
lemma martingale_part_add_ae_eq [sigma_finite_filtration μ ℱ] {f g : ℕ → Ω → E}
  (hf : martingale f ℱ μ) (hg : adapted ℱ (λ n, g (n + 1))) (hg0 : g 0 = 0)
  (hgint : ∀ n, integrable (g n) μ) (n : ℕ) :
  martingale_part (f + g) ℱ μ n =ᵐ[μ] f n :=
begin
  set h := f - martingale_part (f + g) ℱ μ with hhdef,
  have hh : h = predictable_part (f + g) ℱ μ - g,
  { rw [hhdef, sub_eq_sub_iff_add_eq_add, add_comm (predictable_part (f + g) ℱ μ),
      martingale_part_add_predictable_part] },
  have hhpred : adapted ℱ (λ n, h (n + 1)),
  { rw hh,
    exact adapted_predictable_part.sub hg },
  have hhmgle : martingale h ℱ μ := hf.sub (martingale_martingale_part
    (hf.adapted.add $ predictable.adapted hg $ hg0.symm ▸ strongly_measurable_zero) $
    λ n, (hf.integrable n).add $ hgint n),
  refine (eventually_eq_iff_sub.2 _).symm,
  filter_upwards [hhmgle.eq_zero_of_predictable hhpred n] with ω hω,
  rw [hhdef, pi.sub_apply] at hω,
  rw [hω, pi.sub_apply, martingale_part],
  simp [hg0],
end

lemma predictable_part_add_ae_eq [sigma_finite_filtration μ ℱ] {f g : ℕ → Ω → E}
  (hf : martingale f ℱ μ) (hg : adapted ℱ (λ n, g (n + 1))) (hg0 : g 0 = 0)
  (hgint : ∀ n, integrable (g n) μ) (n : ℕ) :
  predictable_part (f + g) ℱ μ n =ᵐ[μ] g n :=
begin
  filter_upwards [martingale_part_add_ae_eq hf hg hg0 hgint n] with ω hω,
  rw ← add_right_inj (f n ω),
  conv_rhs { rw [← pi.add_apply, ← pi.add_apply,
    ← martingale_part_add_predictable_part ℱ μ (f + g)] },
  rw [pi.add_apply, pi.add_apply, hω],
end

section difference

lemma predictable_part_bdd_difference {R : ℝ≥0} {f : ℕ → Ω → ℝ}
  (ℱ : filtration ℕ m0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
  ∀ᵐ ω ∂μ, ∀ i, |predictable_part f ℱ μ (i + 1) ω - predictable_part f ℱ μ i ω| ≤ R :=
begin
  simp_rw [predictable_part, finset.sum_apply, finset.sum_range_succ_sub_sum],
  exact ae_all_iff.2 (λ i, ae_bdd_condexp_of_ae_bdd $ ae_all_iff.1 hbdd i),
end

lemma martingale_part_bdd_difference {R : ℝ≥0} {f : ℕ → Ω → ℝ}
  (ℱ : filtration ℕ m0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
  ∀ᵐ ω ∂μ, ∀ i, |martingale_part f ℱ μ (i + 1) ω - martingale_part f ℱ μ i ω| ≤ ↑(2 * R) :=
begin
  filter_upwards [hbdd, predictable_part_bdd_difference ℱ hbdd] with ω hω₁ hω₂ i,
  simp only [two_mul, martingale_part, pi.sub_apply],
  have : |f (i + 1) ω - predictable_part f ℱ μ (i + 1) ω - (f i ω - predictable_part f ℱ μ i ω)| =
    |(f (i + 1) ω - f i ω) - (predictable_part f ℱ μ (i + 1) ω - predictable_part f ℱ μ i ω)|,
  { ring_nf }, -- `ring` suggests `ring_nf` despite proving the goal
  rw this,
  exact (abs_sub _ _).trans (add_le_add (hω₁ i) (hω₂ i)),
end

end difference

end measure_theory
