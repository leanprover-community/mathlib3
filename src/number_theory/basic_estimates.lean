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

-- TODO (BM): Put this in mathlib
lemma finset.Icc_subset_Icc {α : Type*} [preorder α] [locally_finite_order α]
  {a₁ a₂ b₁ b₂ : α} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
  finset.Icc a₁ b₁ ⊆ finset.Icc a₂ b₂ :=
begin
  intros x hx,
  simp only [finset.mem_Icc] at ⊢ hx,
  exact ⟨ha.trans hx.1, hx.2.trans hb⟩,
end

-- TODO (BM): Put this in mathlib
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
  (finset.sum_le_sum_of_subset_of_nonneg
    (finset.Icc_subset_Icc le_rfl (le_floor_of_le hx)) (by simp))

@[measurability] lemma measurable_summatory {M : Type*} [add_comm_monoid M] [measurable_space M]
  {a : ℕ → M} :
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
def euler_mascheroni : ℝ := 1 - ∫ t in Ioi 1, int.fract t * (t^2)⁻¹

open filter asymptotics

-- TODO (BM): Put this in mathlib
lemma Ici_diff_Icc {a b : ℝ} (hab : a ≤ b) : Ici a \ Icc a b = Ioi b :=
begin
  rw [←Icc_union_Ioi_eq_Ici hab, union_diff_left, sdiff_eq_self_iff_disjoint],
  rintro x ⟨⟨_, hx⟩, hx'⟩,
  exact not_le_of_lt hx' hx,
end

lemma Ioi_diff_Icc {a b : ℝ} (hab : a ≤ b) : Ioi a \ Ioc a b = Ioi b :=
begin
  rw [←Ioc_union_Ioi_eq_Ioi hab, union_diff_left, diff_eq_self, subset_def],
  simp,
end

open_locale nnreal filter topological_space

lemma integral_Ioi_rpow_tendsto_aux {a r : ℝ} (hr : r < -1) (ha : 0 < a)
  {ι : Type*} {b : ι → ℝ} {l : filter ι} (hb : tendsto b l at_top) :
  tendsto (λ i, ∫ x in a..b i, x ^ r) l (nhds (-a ^ (r + 1) / (r + 1))) :=
begin
  suffices :
    tendsto (λ i, ∫ x in a..b i, x ^ r) l (nhds (0 / (r + 1) - a ^ (r + 1) / (r + 1))),
  { simpa [neg_div] using this },
  have : ∀ᶠ i in l, ∫ x in a..b i, x ^ r = (b i) ^ (r + 1) / (r + 1) - a ^ (r + 1) / (r + 1),
  { filter_upwards [hb.eventually (eventually_ge_at_top a)],
    intros i hi,
    rw [←sub_div, ←integral_rpow (or.inr ⟨hr.ne, not_mem_interval_of_lt ha (ha.trans_le hi)⟩)], },
  rw tendsto_congr' this,
  refine tendsto.sub_const _ (tendsto.div_const _),
  rw ←neg_neg (r+1),
  apply (tendsto_rpow_neg_at_top _).comp hb,
  simpa using hr
end

lemma integrable_on_rpow_Ioi {a r : ℝ} (hr : r < -1) (ha : 0 < a) :
  integrable_on (λ x, x ^ r) (Ioi a) :=
begin
  have hb : tendsto (λ (x : ℝ≥0), a + x) at_top at_top :=
    tendsto_at_top_add_const_left _ _ (nnreal.tendsto_coe_at_top.2 tendsto_id),
  have : tendsto (λ (i : ℝ≥0), ∫ x in a..(a + i), ∥x ^ r∥) at_top (nhds (-a ^ (r + 1) / (r + 1))),
  { refine (integral_Ioi_rpow_tendsto_aux hr ha hb).congr (λ x, _),
    refine interval_integral.integral_congr (λ i hi, _),
    apply (real.norm_of_nonneg (real.rpow_nonneg_of_nonneg _ _)).symm,
    exact ha.le.trans ((by simp : _ ≤ _).trans hi.1) },
  refine integrable_on_Ioi_of_interval_integral_norm_tendsto _ _ (λ i, _) hb this,
  refine (continuous_on.integrable_on_Icc _).mono_set Ioc_subset_Icc_self,
  exact continuous_on_id.rpow_const (λ x hx, or.inl (ha.trans_le hx.1).ne'),
end

lemma integral_rpow_Ioi {a r : ℝ} (hr : r < -1) (ha : 0 < a) :
  ∫ x in Ioi a, x ^ r = - a ^ (r + 1) / (r + 1) :=
tendsto_nhds_unique
  (interval_integral_tendsto_integral_Ioi _ (integrable_on_rpow_Ioi hr ha) tendsto_id)
  (integral_Ioi_rpow_tendsto_aux hr ha tendsto_id)

lemma integrable_on_rpow_inv_Ioi {a r : ℝ} (hr : 1 < r) (ha : 0 < a) :
  integrable_on (λ x, (x ^ r)⁻¹) (Ioi a) :=
(integrable_on_rpow_Ioi (neg_lt_neg hr) ha).congr_fun (λ x hx, rpow_neg (ha.trans hx).le _)
  measurable_set_Ioi

lemma integral_rpow_inv {a r : ℝ} (hr : 1 < r) (ha : 0 < a) :
  ∫ x in Ioi a, (x ^ r)⁻¹ = a ^ (1 - r) / (r - 1) :=
begin
  rw [←set_integral_congr, integral_rpow_Ioi (neg_lt_neg hr) ha, neg_div, ←div_neg, neg_add',
    neg_neg, neg_add_eq_sub],
  { apply measurable_set_Ioi },
  exact λ x hx, (rpow_neg (ha.trans hx).le _)
end

lemma integrable_on_zpow_Ioi {a : ℝ} {n : ℤ} (hn : n < -1) (ha : 0 < a) :
  integrable_on (λ x, x ^ n) (Ioi a) :=
by exact_mod_cast integrable_on_rpow_Ioi (show (n : ℝ) < -1, by exact_mod_cast hn) ha

lemma integral_zpow_Ioi {a : ℝ} {n : ℤ} (hn : n < -1) (ha : 0 < a) :
  ∫ x in Ioi a, x ^ n = - a ^ (n + 1) / (n + 1) :=
by exact_mod_cast integral_rpow_Ioi (show (n : ℝ) < -1, by exact_mod_cast hn) ha

lemma integrable_on_zpow_inv_Ioi {a : ℝ} {n : ℤ} (hn : 1 < n) (ha : 0 < a) :
  integrable_on (λ x, (x ^ n)⁻¹) (Ioi a) :=
(integrable_on_zpow_Ioi (neg_lt_neg hn) ha).congr_fun (by simp) measurable_set_Ioi

lemma integral_zpow_inv_Ioi {a : ℝ} {n : ℤ} (hn : 1 < n) (ha : 0 < a) :
  ∫ x in Ioi a, (x ^ n)⁻¹ = a ^ (1 - n) / (n - 1) :=
begin
  simp_rw [←zpow_neg₀, integral_zpow_Ioi (neg_lt_neg hn) ha, neg_div, ←div_neg, neg_add',
    int.cast_neg, neg_neg, neg_add_eq_sub],
end

lemma integrable_on_pow_inv_Ioi {a : ℝ} {n : ℕ} (hn : 1 < n) (ha : 0 < a) :
  integrable_on (λ x, (x ^ n)⁻¹) (Ioi a) :=
by exact_mod_cast integrable_on_zpow_inv_Ioi (show 1 < (n : ℤ), by exact_mod_cast hn) ha

lemma integral_pow_inv_Ioi {a : ℝ} {n : ℕ} (hn : 1 < n) (ha : 0 < a) :
  ∫ x in Ioi a, (x ^ n)⁻¹ = (a ^ (n - 1))⁻¹ / (n - 1) :=
by simp_rw [←zpow_coe_nat, integral_zpow_inv_Ioi (show 1 < (n : ℤ), by exact_mod_cast hn) ha,
  int.cast_coe_nat, ←zpow_neg₀, int.coe_nat_sub hn.le, neg_sub, int.coe_nat_one]

lemma fract_mul_integrable {f : ℝ → ℝ} (s : set ℝ)
  (hf' : integrable_on f s) :
  integrable_on (int.fract * f) s :=
begin
  refine integrable.mono hf' _ (eventually_of_forall _),
  { exact measurable_id'.fract.ae_measurable.mul' hf'.1 },
  intro x,
  simp only [normed_field.norm_mul, pi.mul_apply, norm_of_nonneg (int.fract_nonneg _)],
  exact mul_le_of_le_one_left (norm_nonneg _) (int.fract_lt_one _).le,
end

lemma euler_mascheroni_convergence_rate :
  is_O_with 1 (λ (x : ℝ), 1 - (∫ t in Ioc 1 x, int.fract t * (t^2)⁻¹) - euler_mascheroni)
    (λ x, x⁻¹) at_top :=
begin
  apply is_O_with.of_bound,
  rw eventually_at_top,
  refine ⟨1, λ x (hx : _ ≤ _), _⟩,
  have : ∀ t ∈ Ioi (1:ℝ), int.fract t * (t^2)⁻¹ ≤ (t^2)⁻¹,
  { intros t ht,
    refine (mul_le_iff_le_one_left _).2 (int.fract_lt_one _).le,
    rw inv_pos,
    exact sq_pos_of_pos (zero_lt_one.trans ht) },
  have h : integrable_on (λ (x : ℝ), int.fract x * (x ^ 2)⁻¹) (Ioi 1),
  { apply fract_mul_integrable,
    apply integrable_on_pow_inv_Ioi one_lt_two zero_lt_one },
  rw [one_mul, euler_mascheroni, norm_of_nonneg (inv_nonneg.2 (zero_le_one.trans hx)),
    sub_sub_sub_cancel_left, ←integral_diff measurable_set_Ioi measurable_set_Ioc h
    (h.mono_set Ioc_subset_Ioi_self) Ioc_subset_Ioi_self, Ioi_diff_Icc hx,
    norm_of_nonneg],
  { apply (set_integral_mono_on (h.mono_set (Ioi_subset_Ioi hx))
      (integrable_on_pow_inv_Ioi one_lt_two (zero_lt_one.trans_le hx)) measurable_set_Ioi _).trans,
    { rw integral_pow_inv_Ioi one_lt_two (zero_lt_one.trans_le hx),
      norm_num },
    { intros t ht,
      apply this t (Ioi_subset_Ioi hx ht) } },
  exact set_integral_nonneg measurable_set_Ioi
    (λ t ht, div_nonneg (int.fract_nonneg _) (sq_nonneg _)),
end

lemma euler_mascheroni_integral_Ioc_convergence :
  tendsto (λ (x : ℝ), 1 - ∫ t in Ioc 1 x, int.fract t * (t^2)⁻¹) at_top (𝓝 euler_mascheroni) :=
by simpa using
  (euler_mascheroni_convergence_rate.is_O.trans_tendsto tendsto_inv_at_top_zero).add_const
    euler_mascheroni

lemma euler_mascheroni_interval_integral_convergence :
  tendsto (λ (x : ℝ), (1 : ℝ) - ∫ t in 1..x, int.fract t * (t^2)⁻¹) at_top (𝓝 euler_mascheroni) :=
begin
  apply euler_mascheroni_integral_Ioc_convergence.congr' _,
  rw [eventually_eq, eventually_at_top],
  exact ⟨1, λ x hx, by rw interval_integral.integral_of_le hx⟩,
end

lemma nat_floor_eq_int_floor {α : Type*} [linear_ordered_ring α] [floor_ring α]
  {y : α} (hy : 0 ≤ y) : (⌊y⌋₊ : ℤ) = ⌊y⌋ :=
begin
  rw [eq_comm, int.floor_eq_iff, int.cast_coe_nat],
  exact ⟨nat.floor_le hy, nat.lt_floor_add_one y⟩,
end

lemma harmonic_series_is_O_aux {x : ℝ} (hx : 1 ≤ x) :
  summatory (λ i, (i : ℝ)⁻¹) x - log x - euler_mascheroni =
    (1 - (∫ t in Ioc 1 x, int.fract t * (t^2)⁻¹) - euler_mascheroni) - int.fract x * x⁻¹ :=
begin
  have floor_eq : ∀ (x : ℝ), 0 ≤ x → summatory (λ _, (1 : ℝ)) x = ((⌊x⌋ : ℤ) : ℝ),
  { intros y hy,
    rw [summatory, finset.sum_const, nat.card_Icc, nat.smul_one_eq_coe, nat.add_sub_cancel,
      ←nat_floor_eq_int_floor hy, int.cast_coe_nat] },
  have diff : (∀ (i ∈ Ici (1:ℝ)), has_deriv_at (λ x, x⁻¹) (-(i ^ 2)⁻¹) i),
  { rintro i (hi : (1:ℝ) ≤ _),
    apply has_deriv_at_inv (zero_lt_one.trans_le hi).ne' },
  have cont : continuous_on (λ (i : ℝ), (i ^ 2)⁻¹) (Ici 1),
  { refine ((continuous_pow 2).continuous_on.inv₀ _),
    rintro i (hi : _ ≤ _),
    exact (pow_ne_zero_iff nat.succ_pos').2 (zero_lt_one.trans_le hi).ne' },
  have ps := partial_summation_cont' (λ _, (1 : ℝ)) _ _ diff cont.neg x,
  simp only [one_mul] at ps,
  simp only [ps, integral_Icc_eq_integral_Ioc],
  rw [floor_eq _ (zero_le_one.trans hx), ←int.self_sub_floor, sub_mul,
    mul_inv_cancel (zero_lt_one.trans_le hx).ne', sub_sub (1 : ℝ), sub_sub_sub_cancel_left, sub_sub,
    sub_sub, sub_right_inj, ←add_assoc, add_left_inj, ←eq_sub_iff_add_eq', ←integral_sub],
  rotate,
  { apply fract_mul_integrable,
    exact (cont.mono Icc_subset_Ici_self).integrable_on_Icc.mono_set Ioc_subset_Icc_self },
  { refine integrable_on.congr_set_ae _ Ioc_ae_eq_Icc,
    exact partial_summation_integrable _ (cont.neg.mono Icc_subset_Ici_self).integrable_on_Icc },
  have : eq_on (λ a : ℝ, int.fract a * (a ^ 2)⁻¹ - summatory (λ _, (1 : ℝ)) a * -(a ^ 2)⁻¹)
    (λ y : ℝ, y⁻¹) (Ioc 1 x),
  { intros y hy,
    dsimp,
    have : 0 < y := zero_lt_one.trans hy.1,
    rw [floor_eq _ this.le, mul_neg_eq_neg_mul_symm, sub_neg_eq_add, ←add_mul, int.fract_add_floor,
      sq, mul_inv₀, mul_inv_cancel_left₀ this.ne'] },
  rw [set_integral_congr measurable_set_Ioc this, ←interval_integral.integral_of_le hx,
    integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx), div_one],
end

lemma fract_mul_norm_le (f : ℝ → ℝ) {x : ℝ} :
  ∥int.fract x * f x∥ ≤ ∥f x∥ :=
begin
  simp only [normed_field.norm_mul],
  apply mul_le_of_le_one_left (norm_nonneg _),
  simp only [norm_of_nonneg, int.fract_nonneg _, (int.fract_lt_one x).le],
end

lemma is_O_with_one_fract_mul (f : ℝ → ℝ) :
  is_O_with 1 (λ (x : ℝ), int.fract x * f x) f at_top :=
begin
  apply is_O_with.of_bound (eventually_of_forall _),
  intro x,
  simp only [one_mul],
  apply fract_mul_norm_le,
end

lemma harmonic_series_is_O_with :
  is_O_with 2 (λ x, summatory (λ i, (i : ℝ)⁻¹) x - log x - euler_mascheroni) (λ x, x⁻¹) at_top :=
begin
  have : is_O_with 1 (λ (x : ℝ), int.fract x * x⁻¹) (λ x, x⁻¹) at_top := is_O_with_one_fract_mul _,
  refine (euler_mascheroni_convergence_rate.sub this).congr' _ _ eventually_eq.rfl,
  { norm_num }, -- I seriously need to prove 1 + 1 = 2
  filter_upwards [eventually_ge_at_top (1 : ℝ)],
  intros x hx,
  exact (harmonic_series_is_O_aux hx).symm,
end

lemma harmonic_series_real_limit :
  tendsto (λ x, (∑ i in finset.Icc 1 ⌊x⌋₊, (i : ℝ)⁻¹) - log x) at_top (𝓝 euler_mascheroni) :=
by simpa using
  (harmonic_series_is_O_with.is_O.trans_tendsto tendsto_inv_at_top_zero).add_const euler_mascheroni

lemma harmonic_series_limit :
  tendsto (λ (n : ℕ), (∑ i in finset.Icc 1 n, (i : ℝ)⁻¹) - log n) at_top (𝓝 euler_mascheroni) :=
(harmonic_series_real_limit.comp tendsto_coe_nat_at_top_at_top).congr (λ x, by simp)

lemma summatory_log_aux {x : ℝ} (hx : 1 ≤ x) :
  summatory (λ i, log i) x - (x * log x - x) =
    1 + ((∫ t in 1..x, int.fract t * t⁻¹) - int.fract x * log x) :=
begin
  rw interval_integral.integral_of_le hx,
  have floor_eq : ∀ (x : ℝ), 0 ≤ x → summatory (λ _, (1 : ℝ)) x = ((⌊x⌋ : ℤ) : ℝ),
  { intros y hy,
    rw [summatory, finset.sum_const, nat.card_Icc, nat.smul_one_eq_coe, nat.add_sub_cancel,
      ←nat_floor_eq_int_floor hy, int.cast_coe_nat] },
  have diff : (∀ (i ∈ Ici (1:ℝ)), has_deriv_at log (i⁻¹) i),
  { rintro i (hi : (1:ℝ) ≤ _),
    exact has_deriv_at_log (zero_lt_one.trans_le hi).ne' },
  have cont : continuous_on (λ x : ℝ, x⁻¹) (Ici 1),
  { exact continuous_on_inv₀.mono  (λ x (hx : _ ≤ _), (zero_lt_one.trans_le hx).ne') },
  have ps := partial_summation_cont' (λ _, (1 : ℝ)) _ _ diff cont x,
  simp only [one_mul] at ps,
  simp only [ps, integral_Icc_eq_integral_Ioc],
  clear ps,
  rw [floor_eq _ (zero_le_one.trans hx), ←int.self_sub_fract, sub_mul, sub_sub (x * log x),
    sub_sub_sub_cancel_left, sub_eq_iff_eq_add, add_assoc, ←sub_eq_iff_eq_add', ←add_assoc,
    sub_add_cancel, ←integral_add],
  rotate,
  { apply fract_mul_integrable,
    exact (cont.mono Icc_subset_Ici_self).integrable_on_Icc.mono_set Ioc_subset_Icc_self },
  { apply (partial_summation_integrable _ _).mono_set Ioc_subset_Icc_self,
    exact (cont.mono Icc_subset_Ici_self).integrable_on_Icc },
  rw [←integral_one, interval_integral.integral_of_le hx, set_integral_congr],
  { apply measurable_set_Ioc },
  intros y hy,
  have hy' : 0 < y := zero_lt_one.trans hy.1,
  rw [←add_mul, floor_eq _ hy'.le, int.fract_add_floor, mul_inv_cancel hy'.ne'],
end

lemma is_o_one_of_tendsto_at_top (f : ℝ → ℝ) (l : filter ℝ) (h : tendsto f l at_top) :
  is_o (λ (x : ℝ), (1 : ℝ)) f l :=
begin
  rw is_o_iff,
  intros ε hε,
  have : ∀ᶠ (x : ℝ) in at_top, ∥(1 : ℝ)∥ ≤ ε * ∥x∥,
  { filter_upwards [eventually_ge_at_top ε⁻¹, eventually_ge_at_top (0:ℝ)],
    intros x hx₁ hx₂,
    rwa [norm_one, norm_of_nonneg hx₂, ←inv_pos_le_iff_one_le_mul' hε] },
  exact h.eventually this,
end

lemma is_o_one_log : is_o (λ (x : ℝ), (1 : ℝ)) log at_top :=
is_o_one_of_tendsto_at_top _ _ tendsto_log_at_top

-- lemma integral_mono_on {α β : Type*} (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b)
--   [topological_space α] [opens_measurable_space α] [order_closed_topology α]
--   (h : ∀ x ∈ Icc a b, f x ≤ g x) :
--   ∫ u in a..b, f u ∂μ ≤ ∫ u in a..b, g u ∂μ :=
-- let H := λ x hx, h x $ Ioc_subset_Icc_self hx in
-- by simpa only [integral_of_le hab] using set_integral_mono_on hf.1 hg.1 measurable_set_Ioc H

lemma summatory_log {c : ℝ} (hc : 2 < c) :
  is_O_with c (λ x, summatory (λ i, log i) x - (x * log x - x)) (λ x, log x) at_top :=
begin
  have f₁ : is_O_with 1 (λ (x : ℝ), int.fract x * log x) (λ x, log x) at_top :=
    is_O_with_one_fract_mul _,
  have f₂ : is_o (λ (x : ℝ), (1 : ℝ)) log at_top := is_o_one_log,
  have f₃ : is_O_with 1 (λ (x : ℝ), ∫ t in 1..x, int.fract t * t⁻¹) log at_top,
  { simp only [is_O_with_iff, eventually_at_top, ge_iff_le, one_mul],
    refine ⟨1, λ x hx, _⟩,
    rw [norm_of_nonneg (log_nonneg hx), norm_of_nonneg, ←div_one x,
      ←integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx), div_one],
    swap,
    { apply interval_integral.integral_nonneg hx,
      intros y hy,
      exact mul_nonneg (int.fract_nonneg _) (inv_nonneg.2 (zero_le_one.trans hy.1)) },
    { have h₁ : interval_integrable (λ (u : ℝ), u⁻¹) volume 1 x,
      { refine interval_integral.interval_integrable_inv _ continuous_on_id,
        intros y hy,
        rw interval_of_le hx at hy,
        exact (zero_lt_one.trans_le hy.1).ne' },
      have h₂ : ∀ y ∈ Icc 1 x, int.fract y * y⁻¹ ≤ y⁻¹,
      { intros y hy,
        refine mul_le_of_le_one_left (inv_nonneg.2 _) (int.fract_lt_one _).le,
        exact zero_le_one.trans hy.1 },
      apply interval_integral.integral_mono_on hx _ h₁ h₂,
      { refine h₁.mono_fun' (by measurability) _,
        rw [eventually_le, ae_restrict_iff'],
        { apply eventually_of_forall,
          intros y hy,
          rw interval_oc_of_le hx at hy,
          rw [normed_field.norm_mul, normed_field.norm_inv, norm_of_nonneg (int.fract_nonneg _),
            norm_of_nonneg (zero_le_one.trans hy.1.le)],
          apply h₂,
          exact Ioc_subset_Icc_self hy },
        exact measurable_set_interval_oc } } },
  apply (f₂.add_is_O_with (f₃.sub f₁) _).congr' rfl _ eventually_eq.rfl,
  { rw [eventually_eq, eventually_at_top],
    exact ⟨1, λ x hx, (summatory_log_aux hx).symm⟩ },
  norm_num [hc]
end

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

#exit

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
