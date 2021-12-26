/-
Copyright (c) 2021 Thomas Bloom, Alex Kontorovich, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bloom, Alex Kontorovich, Bhavik Mehta
-/

import analysis.special_functions.integrals
import analysis.special_functions.pow
import number_theory.arithmetic_function
import measure_theory.function.floor
import measure_theory.integral.integral_eq_improper

noncomputable theory

open_locale big_operators
open real set

/--
Given a function `a : ℕ → M` from the naturals into an additive commutative monoid, this expresses
∑ 1 ≤ n ≤ x, a(n).
-/
-- BM: Formally I wrote this as the sum over the naturals in the closed interval `[1, ⌊x⌋]`.
-- The version in the notes uses sums from 1, mathlib typically uses sums from zero - hopefully
-- this difference shouldn't cause serious issues
def summatory {M : Type*} [add_comm_monoid M] (a : ℕ → M) (x : ℝ) : M :=
∑ n in finset.Icc 1 ⌊x⌋₊, a n

lemma summatory_nat {M : Type*} [add_comm_monoid M] (a : ℕ → M) (n : ℕ) :
  summatory a n = ∑ i in finset.Icc 1 n, a i :=
by simp only [summatory, nat.floor_coe]

lemma summatory_eq_floor {M : Type*} [add_comm_monoid M] (a : ℕ → M) (x : ℝ) :
  summatory a x = summatory a ⌊x⌋₊ :=
by rw [summatory, summatory, nat.floor_coe]

lemma summatory_eq_of_Ico {M : Type*} [add_comm_monoid M] (a : ℕ → M) {n : ℕ} {x : ℝ}
  (hx : x ∈ Ico (n : ℝ) (n + 1)) :
  summatory a x = summatory a n :=
by rw [summatory_eq_floor, nat.floor_eq_on_Ico' _ _ hx]

lemma summatory_eq_of_lt_one {M : Type*} [add_comm_monoid M] (a : ℕ → M) {x : ℝ} (hx : x < 1) :
  summatory a x = 0 :=
begin
  rw [summatory, finset.Icc_eq_empty_of_lt, finset.sum_empty],
  rwa [nat.floor_lt' one_ne_zero, nat.cast_one],
end

@[simp] lemma summatory_zero {M : Type*} [add_comm_monoid M] (a : ℕ → M) : summatory a 0 = 0 :=
summatory_eq_of_lt_one _ zero_lt_one

@[simp] lemma summatory_one {M : Type*} [add_comm_monoid M] (a : ℕ → M) : summatory a 1 = a 1 :=
by simp [summatory]

lemma summatory_succ_sub {M : Type*} [add_comm_group M] (a : ℕ → M) (n : ℕ) :
  a (n + 1) = summatory a (n + 1) - summatory a n :=
begin
  rw [←nat.cast_add_one, summatory_nat, summatory_nat, ←nat.Ico_succ_right,
    finset.sum_Ico_succ_top, nat.Ico_succ_right, add_sub_cancel'],
  simp,
end

lemma summatory_eq_sub {M : Type*} [add_comm_group M] (a : ℕ → M) :
  ∀ n, n ≠ 0 → a n = summatory a n - summatory a (n - 1)
| 0 h := (h rfl).elim
| (n+1) _ := by simpa using summatory_succ_sub a n

lemma abs_summatory_le_sum {M : Type*} [semi_normed_group M] (a : ℕ → M) {x : ℝ} :
  ∥summatory a x∥ ≤ ∑ i in finset.Icc 1 ⌊x⌋₊, ∥a i∥ :=
norm_sum_le _ _

lemma finset.Icc_subset_Icc {α : Type*} [preorder α] [locally_finite_order α]
  {a₁ a₂ b₁ b₂ : α} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
  finset.Icc a₁ b₁ ⊆ finset.Icc a₂ b₂ :=
begin
  intros x hx,
  simp only [finset.mem_Icc] at ⊢ hx,
  exact ⟨ha.trans hx.1, hx.2.trans hb⟩,
end

lemma le_floor_of_le {α : Type*} [linear_ordered_semiring α] [floor_semiring α] {n : ℕ} {a : α}
  (h : a ≤ n) : ⌊a⌋₊ ≤ n :=
(le_total a 0).elim
  (λ h', (nat.floor_of_nonpos h').le.trans (nat.zero_le _))
  (λ h', nat.cast_le.1 ((nat.floor_le h').trans h))

open measure_theory

lemma abs_summatory_bound {M : Type*} [semi_normed_group M] (a : ℕ → M) (k : ℕ)
  {x : ℝ} (hx : x ≤ k) :
  ∥summatory a x∥ ≤ ∑ i in finset.Icc 1 k, ∥a i∥ :=
(abs_summatory_le_sum a).trans
  (finset.sum_le_sum_of_subset_of_nonneg (finset.Icc_subset_Icc le_rfl (le_floor_of_le hx)) (by simp))

@[measurability] lemma measurable_summatory {M : Type*} [add_comm_monoid M] [measurable_space M] {a : ℕ → M} :
  measurable (summatory a) :=
begin
  change measurable ((λ y, ∑ i in finset.Icc 1 y, a i) ∘ _),
  exact measurable_from_nat.comp nat.measurable_floor,
end

lemma partial_summation_integrable {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) {f : ℝ → 𝕜} {x y : ℝ}
  (hf' : measure_theory.integrable_on f (Icc x y)) :
  measure_theory.integrable_on (summatory a * f) (Icc x y) :=
begin
  let b := ∑ i in finset.Icc 1 ⌈y⌉₊, ∥a i∥,
  have : integrable_on (b • f) (Icc x y) := integrable.smul b hf',
  refine this.integrable.mono (measurable_summatory.ae_measurable.mul' hf'.1) _,
  rw measure_theory.ae_restrict_iff' (measurable_set_Icc : measurable_set (Icc x _)),
  refine filter.eventually_of_forall (λ z hz, _),
  rw [pi.mul_apply, normed_field.norm_mul, pi.smul_apply, norm_smul],
  refine mul_le_mul_of_nonneg_right ((abs_summatory_bound _ ⌈y⌉₊ _).trans _) (norm_nonneg _),
  { exact hz.2.trans (nat.le_ceil y) },
  rw real.norm_eq_abs,
  exact le_abs_self b,
end

/-- A version of partial summation where the upper bound is a natural number, useful to prove the
general case. -/
theorem partial_summation_nat {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
  {N : ℕ} (hN : 1 ≤ N)
  (hf : ∀ i ∈ Icc (1:ℝ) N, has_deriv_at f (f' i) i) (hf' : integrable_on f' (Icc 1 N)) :
  ∑ n in finset.Icc 1 N, a n * f n =
    summatory a N * f N - ∫ t in Icc (1:ℝ) N, summatory a t * f' t :=
begin
  rw ←nat.Ico_succ_right,
  induction N with N ih,
  { simpa only [le_zero_iff] using hN },
  rcases N.eq_zero_or_pos with rfl | hN',
  { simp },
  have hN'' : (N:ℝ) ≤ N + 1 := by simp only [zero_le_one, le_add_iff_nonneg_right],
  have : Icc (1:ℝ) (N+1) = Icc 1 N ∪ Icc N (N+1),
  { refine (Icc_union_Icc_eq_Icc _ hN'').symm,
    exact nat.one_le_cast.2 hN' },
  simp only [nat.cast_succ, this, mem_union_eq, or_imp_distrib, forall_and_distrib,
    integrable_on_union] at ih hf hf' ⊢,
  rw [finset.sum_Ico_succ_top nat.succ_pos', ih hN' hf.1 hf'.1, add_comm, nat.succ_eq_add_one,
    summatory_succ_sub a, sub_mul, sub_add_eq_add_sub, eq_sub_iff_add_eq, add_sub_assoc, add_assoc,
    nat.cast_add_one, add_right_eq_self, sub_add_eq_add_sub, sub_eq_zero, add_comm, ←add_sub_assoc,
    ←sub_add_eq_add_sub, ←eq_sub_iff_add_eq, ←mul_sub,
    integral_union_ae _ (measurable_set_Icc : measurable_set (Icc (_:ℝ) _)) measurable_set_Icc,
    add_sub_cancel', ←set_integral_congr_set_ae (Ico_ae_eq_Icc' volume_singleton)],
  { have : eq_on (λ x, summatory a x * f' x) (λ x, summatory a N • f' x) (Ico N (N+1)) :=
      λ x hx, congr_arg2 (*) (summatory_eq_of_Ico _ hx) rfl,
    rw [set_integral_congr measurable_set_Ico this, integral_smul, algebra.id.smul_eq_mul,
      set_integral_congr_set_ae (Ico_ae_eq_Ioc' volume_singleton volume_singleton),
      ←interval_integral.integral_of_le hN'', interval_integral.integral_eq_sub_of_has_deriv_at],
    { rw interval_of_le hN'',
      exact hf.2 },
    { exact (interval_integral.interval_integrable_iff_integrable_Icc_of_le hN'').2 hf'.2 } },
  { exact partial_summation_integrable a hf'.1 },
  { exact partial_summation_integrable a hf'.2 },
  { rw [Icc_inter_Icc_eq_singleton _ hN'', ae_eq_empty, volume_singleton],
    exact nat.one_le_cast.2 hN' },
end

/--
Right now this works for functions taking values in R or C, I think it should work for more target
spaces.
-/
theorem partial_summation {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜) {x : ℝ}
  (hf : ∀ i ∈ Icc (1:ℝ) x, has_deriv_at f (f' i) i) (hf' : integrable_on f' (Icc 1 x)) :
  summatory (λ n, a n * f n) x = summatory a x * f x - ∫ t in Icc 1 x, summatory a t * f' t :=
begin
  cases lt_or_le x 1,
  { simp only [h, summatory_eq_of_lt_one _ h, zero_mul, sub_zero, Icc_eq_empty_of_lt,
      integral_zero_measure, measure.restrict_empty] },
  have hx : (1:ℝ) ≤ ⌊x⌋₊,
    by rwa [nat.one_le_cast, nat.le_floor_iff (zero_le_one.trans h), nat.cast_one],
  have hx' : (⌊x⌋₊:ℝ) ≤ x := nat.floor_le (zero_le_one.trans h),
  have : Icc (1:ℝ) x = Icc 1 ⌊x⌋₊ ∪ Icc ⌊x⌋₊ x :=
    (Icc_union_Icc_eq_Icc hx hx').symm,
  simp only [this, integrable_on_union, mem_union, or_imp_distrib, forall_and_distrib] at hf hf' ⊢,
  rw [summatory, partial_summation_nat a f f' (nat.one_le_cast.1 hx) hf.1 hf'.1, eq_comm,
    sub_eq_sub_iff_sub_eq_sub, summatory_eq_floor, ←mul_sub,
    integral_union_ae _ measurable_set_Icc (measurable_set_Icc : measurable_set (Icc _ x)),
    add_sub_cancel'],
  { have : eq_on (λ y, summatory a y * f' y) (λ y, summatory a ⌊x⌋₊ • f' y) (Icc ⌊x⌋₊ x),
    { intros y hy,
      dsimp,
      rw summatory_eq_floor,
      congr' 3,
      exact nat.floor_eq_on_Ico _ _ ⟨hy.1, hy.2.trans_lt (nat.lt_floor_add_one _)⟩ },
    rw [set_integral_congr measurable_set_Icc this, integral_smul, algebra.id.smul_eq_mul,
      ←set_integral_congr_set_ae (Ioc_ae_eq_Icc' volume_singleton),
      ←interval_integral.integral_of_le hx',
      interval_integral.integral_eq_sub_of_has_deriv_at],
    { rw interval_of_le hx',
      exact hf.2 },
    { exact (interval_integral.interval_integrable_iff_integrable_Icc_of_le hx').2 hf'.2 } },
  apply partial_summation_integrable _ hf'.1,
  apply partial_summation_integrable _ hf'.2,
  { rw [Icc_inter_Icc_eq_singleton hx (nat.floor_le (zero_le_one.trans h)), ae_eq_empty,
      volume_singleton] },
end

theorem partial_summation_cont {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜) {x : ℝ}
  (hf : ∀ i ∈ Icc (1:ℝ) x, has_deriv_at f (f' i) i) (hf' : continuous_on f' (Icc 1 x)) :
  summatory (λ n, a n * f n) x = summatory a x * f x - ∫ t in Icc 1 x, summatory a t * f' t :=
partial_summation _ _ _ hf hf'.integrable_on_Icc

/--
A variant of partial summation where we assume differentiability of `f` and integrability of `f'` on
`[1, ∞)` and derive the partial summation equation for all `x`.
-/
theorem partial_summation' {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
  (hf : ∀ i ∈ Ici (1:ℝ), has_deriv_at f (f' i) i) (hf' : integrable_on f' (Ici 1)) {x : ℝ} :
  summatory (λ n, a n * f n) x = summatory a x * f x - ∫ t in Icc 1 x, summatory a t * f' t :=
partial_summation _ _ _ (λ i hi, hf _ hi.1) (hf'.mono_set Icc_subset_Ici_self)

/--
A variant of partial summation where we assume differentiability of `f` and continuity of `f'` on
`[1, ∞)` and derive the partial summation equation for all `x`.
-/
theorem partial_summation_cont' {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
  (hf : ∀ i ∈ Ici (1:ℝ), has_deriv_at f (f' i) i) (hf' : continuous_on f' (Ici 1)) (x : ℝ) :
  summatory (λ n, a n * f n) x = summatory a x * f x - ∫ t in Icc 1 x, summatory a t * f' t :=
partial_summation_cont _ _ _ (λ i hi, hf _ hi.1) (hf'.mono Icc_subset_Ici_self)

-- BM: A definition of the Euler-Mascheroni constant
-- Maybe a different form is a better definition, and in any case it would be nice to show the
-- different definitions are equivalent.
-- This version uses an integral over an infinite interval, which in mathlib is *not* defined
-- as the limit of integrals over finite intervals, but there is a result saying they are equal:
-- see measure_theory.integral.integral_eq_improper: `interval_integral_tendsto_integral_Ioi`
def euler_mascheroni : ℝ := 1 - ∫ t in Ici 1, int.fract t / t^2

open filter asymptotics

lemma Ici_diff_Icc {a b : ℝ} (hab : a ≤ b) : Ici a \ Icc a b = Ioi b :=
begin
  rw [←Icc_union_Ioi_eq_Ici hab, union_diff_left, diff_eq_self],
  rintro x ⟨⟨_, hx⟩, hx'⟩,
  exact not_le_of_lt hx' hx,
end

-- integrable_on_Ioi_of_interval_integral_norm_tendsto

-- lemma interval_integrable_zpow {n : ℤ} (h : 0 ≤ n ∨ (0 : ℝ) ∉ [a, b]) :
--   interval_integrable (λ x, x ^ n) μ a b :=
-- (continuous_on_id.zpow n $ λ x hx, h.symm.imp (ne_of_mem_of_not_mem hx) id).interval_integrable

example : tendsto (λ (x:ℝ), x) at_top at_top :=
begin
  apply tendsto_id,
end

-- lemma euler_mascheroni_tail (x : ℝ) (hx : 1 ≤ x) :
--   ∫ t in Ici x, int.fract t / t^2 ≤ (1:ℝ) / x :=

-- begin
--   calc ∫ (t : ℝ) in Ioi x, int.fract t / t ^ 2 ≤ ∫ (t : ℝ) in Ioi x, (1:ℝ) / t ^ 2 : _
--         ... ≤ (1:ℝ) / x : _,
--           { refine interval_integral.integral_mono_on hx _ _ _,
--             { sorry, },
--             { sorry, },
--             { intros t ht,
--               have non_neg : 0 ≤ (1:ℝ)/t^2 := one_div_nonneg.mpr (sq_nonneg t),
--               calc int.fract t / t ^ 2 = int.fract t * (1 / t ^ 2) : by field_simp
--                 ... ≤ 1 * (1 / t ^ 2) : _
--                 ... ≤ 1 / t ^ 2 : by simp,
--               exact mul_le_mul (le_of_lt (int.fract_lt_one t))
--                 (by simp: (1:ℝ)/t^2 ≤ (1:ℝ)/t^2) non_neg zero_le_one, }, },
--           { sorry, },
-- end

lemma integrable_on_pow :
  integrable_on (λ (x : ℝ), x ^ (-2 : ℤ)) (Ioi 1) :=
begin
  refine integrable_on_Ioi_of_interval_integral_norm_tendsto 1 (1 : ℝ) (λ i, _) tendsto_id _,
  refine (continuous_on.integrable_on_Icc _).mono_set Ioc_subset_Icc_self,
  refine continuous_on_id.zpow _ (λ x hx, or.inl (zero_lt_one.trans_le hx.1).ne'),
  have := integral_zpow,
end

lemma euler_mascheroni_convergence :
  is_O (λ (x : ℝ), 1 - (∫ t in Icc 1 x, int.fract t / t^2) - euler_mascheroni) (λ x, x⁻¹) at_top :=
begin
  apply is_O.of_bound 1,
  rw eventually_at_top,
  refine ⟨1, λ x (hx : _ ≤ _), _⟩,
  have : ∀ t ∈ Ici (1:ℝ), int.fract t / t^2 ≤ (t^2)⁻¹,
  { intros t ht,
    apply (div_le_div_of_le_of_nonneg (int.fract_lt_one t).le (sq_nonneg _)).trans,
    simp },
  have : integrable_on (λ (x : ℝ), (x^2)⁻¹) (Ici 1),
  { have := has_deriv_at_zpow,

  },
  have : integrable_on (λ (x : ℝ), int.fract x / x ^ 2) (Ici 1),
  {

  },
  rw [one_mul, real.norm_eq_abs, real.norm_eq_abs, euler_mascheroni,
    abs_of_nonneg (inv_nonneg.2 (zero_le_one.trans hx)), sub_sub_sub_cancel_left,
    ←integral_diff (@measurable_set_Ici ℝ _ _ _ _ _ _) measurable_set_Icc _ _ Icc_subset_Ici_self,
    Ici_diff_Icc hx],

end

-- vinogradov notation to state things more nicely
-- probably this should be generalised to not be just for ℝ, but I think this works for now
def vinogradov (f : ℝ → ℝ) (g : ℝ → ℝ) : Prop := is_O f g at_top

infix ` ≪ `:50 := vinogradov
-- BM: might want to localise this notation
-- in the measure_theory locale it's used for absolute continuity of measures

-- lemma harmonic_series_estimate :
--   ∃ (g : ℝ → ℝ), is_O g (λ x, x⁻¹) at_top ∧
--     ∀ x, summatory (λ n, (n : ℝ)⁻¹) x = log x + euler_mascheroni + g x :=
-- begin
--   refine ⟨sorry, sorry, λ x, _⟩,
--   have : ∀ x, summatory (λ _, 1) x = ⌊x⌋₊,
--   { intro x,
--     rw [summatory, ←finset.card_eq_sum_ones, nat.card_Icc],
--     refl },
--   have : (∀ (i ∈ Icc 1 x), has_deriv_at (λ y, y ^ (-1:ℤ)) (-i ^ (-2:ℤ)) i),
--   { intros i hi,
--     simpa only [neg_mul_eq_neg_mul_symm, one_mul, int.cast_one, int.cast_neg]
--       using has_deriv_at_zpow (-1) i (or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hi.1))), },
--   have : (0:ℝ) ≤ -2 ∨ (0:ℝ) ∉ interval 1 x,
--   { right,

--   },
--   have := partial_summation (λ _, (1 : ℝ)) _ _ this
--             (interval_integral.interval_integrable_zpow _).neg,
--   simp only [zpow_neg₀, one_mul, interval_integral.integral_neg, zpow_one, mul_neg_eq_neg_mul_symm,
--     sub_neg_eq_add] at this,
--   rw this,

--   -- simp only [one_div],
-- end

-- --   is_O (λ x, summatory (λ i, (1 : ℝ) / i) x - log x - euler_mascheroni) (λ x, 1 / x) at_top
-- --   :=
-- -- begin
-- -- end

lemma harmonic_series_vinogradov :
  is_O (λ x, summatory (λ i, (i : ℝ)⁻¹) x - log x - euler_mascheroni) (λ x, x⁻¹) at_top :=
begin
  -- suffices :
  --   ∀ᶠ x in at_top, summatory (λ i, (i : ℝ)⁻¹) x - log x - euler_mascheroni = _,

  have floor_eq : ∀ x, summatory (λ _, (1 : ℝ)) x = ⌊x⌋₊,
  { intro x,
    rw [summatory, finset.sum_const, nat.card_Icc, nat.smul_one_eq_coe],
    refl },
  have diff : (∀ (i ∈ Ici (1:ℝ)), has_deriv_at (λ x, x⁻¹) (-(i ^ (2:ℤ))⁻¹) i),
  { rintro i (hi : (1:ℝ) ≤ _),
    apply has_deriv_at_inv (zero_lt_one.trans_le hi).ne' },
  have cont : continuous_on (λ (i : ℝ), -(i ^ 2)⁻¹) (Ici 1),
  { refine ((continuous_pow 2).continuous_on.inv₀ _).neg,
    rintro i (hi : _ ≤ _),
    exact (pow_ne_zero_iff nat.succ_pos').2 (zero_lt_one.trans_le hi).ne' },
  have := partial_summation_cont' (λ _, (1 : ℝ)) _ _ diff cont,
  dsimp at this,
  simp only [one_mul, floor_eq] at this,
  simp only [this],
  -- have := partial_summation (λ _, 1) (λ x, x ^ (-1 : ℤ)) (λ x, - x ^ (-2 : ℤ)),
end

lemma summatory_log :
  (λ x, summatory (λ i, log i) x - x * log x) ≪ (λ x, log x) :=
sorry

namespace nat.arithmetic_function
open_locale arithmetic_function

lemma pow_zero_eq_zeta :
  pow 0 = ζ :=
begin
  ext i,
  simp,
end

lemma sigma_zero_eq_zeta_mul_zeta :
  σ 0 = ζ * ζ :=
by rw [←zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]

lemma sigma_zero_apply_eq_sum_divisors {i : ℕ} :
  σ 0 i = ∑ d in i.divisors, 1 :=
begin
  rw [sigma_apply, finset.sum_congr rfl],
  intros x hx,
  apply pow_zero,
end

lemma sigma_zero_apply_eq_card_divisors {i : ℕ} :
  σ 0 i = i.divisors.card :=
 by rw [sigma_zero_apply_eq_sum_divisors, finset.card_eq_sum_ones]

-- BM: Bounds like these make me tempted to define a relation
-- `equal_up_to p f g` to express that `f - g ≪ p` (probably stated `f - g = O(p)`) and show that
-- (for fixed p) this is an equivalence relation, and that it is increasing in `p`
-- Perhaps this would make it easier to express the sorts of calculations that are common in ANT,
-- especially ones like
-- f₁ = f₂ + O(p)
--    = f₃ + O(p)
--    = f₄ + O(p)
-- since this is essentially using transitivity of `equal_up_to p` three times
lemma hyperbola :
  (λ x, summatory (λ i, σ 0 i) x - x * log x - (2 * euler_mascheroni - 1) * x) ≪ sqrt :=
sorry

-- BM: This might need a lower bound on `n`, maybe just `1 ≤ n` is good enough?
lemma divisor_bound :
  ∃ (g : ℝ → ℝ), g ≪ (λ i, 1 / log (log i)) ∧
    ∀ (n : ℕ), (σ 0 n : ℝ) ≤ n ^ g n :=
sorry

-- BM: Might also need a lower bound on `n`?
lemma weak_divisor_bound (ε : ℝ) (hε : 0 < ε) :
  ∃ C, 0 < C ∧ ∀ n, (σ 0 n : ℝ) ≤ C * (n : ℝ)^ε :=
sorry

lemma big_O_divisor_bound (ε : ℝ) (hε : 0 < ε) :
  asymptotics.is_O (λ n, (σ 0 n : ℝ)) (λ n, (n : ℝ)^ε) filter.at_top :=
sorry

-- BM: I have this defined in another branch, coming to mathlib soon
def von_mangoldt : nat.arithmetic_function ℝ := sorry
localized "notation `Λ` := von_mangoldt" in arithmetic_function

-- BM: this is equivalent to `is_O (λ x, x) (summatory Λ) at_top` (ie the same thing in Landau
-- notation) but the proof gives an explicit bound? So we can show something like
-- `is_O_with c (λ x, x) (summatory Λ) at_top`, with a nice constant `c` (I think the proof I have
-- gives something like c = log 2?)
-- Similarly there's a "for sufficiently large x" hidden in here, we could try to remove that too?
-- Then the statement would be something like
-- lemma explicit_chebyshev_lower (x : ℕ) (hx : x₀ ≤ x) :
--    x ≤ log 2 * summatory Λ x :=
-- which could be helpful
lemma chebyshev_lower :
  (λ x, x) ≪ summatory Λ :=
sorry

-- BM: As above, with c = 2 log 2?
lemma chebyshev_upper :
  summatory Λ ≪ (λ x, x) :=
sorry

/--
Given a function `a : ℕ → M` from the naturals into an additive commutative monoid, this expresses
∑ 1 ≤ p ≤ x, a(p) where `p` is prime.
-/
def prime_summatory {M : Type*} [add_comm_monoid M] (a : ℕ → M) (x : ℝ) : M :=
  ∑ n in (finset.Icc 1 ⌊x⌋₊).filter nat.prime, a n
-- BM: equivalently could say it's `summatory (λ n, if (a n).prime then a n else 0) x`

lemma log_reciprocal :
  (λ x, prime_summatory (λ p, log p / p) x - log x) ≪ (λ _, 1) :=
sorry

lemma prime_counting_asymptotic :
  (λ x, prime_summatory (λ _, 1) x - summatory Λ x / log x) ≪ (λ x, x / (log x)^2) :=
sorry

lemma prime_reciprocal : ∃ b,
  (λ x, prime_summatory (λ p, 1 / p) x - log (log x) - b) ≪ (λ x, 1 / log x) :=
sorry

-- BM: I expect there's a nicer way of stating this but this should be good enough for now
lemma mertens_third :
  ∃ c, (λ x, ∏ p in (finset.Icc 1 ⌊x⌋₊), (1 - 1/p)⁻¹ - c * log x) ≪ (λ _, 1) :=
sorry

end nat.arithmetic_function
