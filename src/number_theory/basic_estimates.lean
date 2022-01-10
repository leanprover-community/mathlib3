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

open_locale big_operators nnreal filter topological_space arithmetic_function

open filter asymptotics real set

section to_mathlib

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

-- TODO (BM): Put this in mathlib
lemma Ici_diff_Icc {a b : ℝ} (hab : a ≤ b) : Ici a \ Icc a b = Ioi b :=
begin
  rw [←Icc_union_Ioi_eq_Ici hab, union_diff_left, diff_eq_self],
  rintro x ⟨⟨_, hx⟩, hx'⟩,
  exact not_le_of_lt hx' hx,
end

-- TODO: Move to mathlib
lemma Ioi_diff_Icc {a b : ℝ} (hab : a ≤ b) : Ioi a \ Ioc a b = Ioi b :=
begin
  rw [←Ioc_union_Ioi_eq_Ioi hab, union_diff_left, diff_eq_self, subset_def],
  simp,
end

lemma is_o_pow_exp_at_top {n : ℕ} (hn : 1 ≤ n) : is_o (λ x, x^n) exp at_top :=
begin
  rw is_o_iff_tendsto (λ x hx, ((exp_pos x).ne' hx).elim),
  simpa using tendsto_div_pow_mul_exp_add_at_top 1 0 n zero_ne_one hn,
end

lemma tendsto_log_div_mul_add_at_top (a b : ℝ) (ha : a ≠ 0) :
  tendsto (λ x, log x / (a * x + b)) at_top (𝓝 0) :=
((tendsto_div_pow_mul_exp_add_at_top a b 1 ha.symm le_rfl).comp tendsto_log_at_top).congr'
  (by filter_upwards [eventually_gt_at_top (0 : ℝ)] (λ x hx, by simp [exp_log hx]))

lemma is_o_log_id_at_top : is_o log (λ x, x) at_top :=
begin
  rw is_o_iff_tendsto (λ x (hx : x = 0), (show log x = 0, by simp [hx])),
  simpa using tendsto_log_div_mul_add_at_top 1 0 one_ne_zero,
end

end to_mathlib

/--
Given a function `a : ℕ → M` from the naturals into an additive commutative monoid, this expresses
∑ 1 ≤ n ≤ x, a(n).
-/
-- BM: Formally I wrote this as the sum over the naturals in the closed interval `[1, ⌊x⌋]`.
-- The version in the notes uses sums from 1, mathlib typically uses sums from zero - hopefully
-- this difference shouldn't cause serious issues

variables {M : Type*} [add_comm_monoid M] (a : ℕ → M)

def summatory (a : ℕ → M) (x : ℝ) : M :=
∑ n in finset.Icc 1 ⌊x⌋₊, a n

lemma summatory_nat (n : ℕ) :
  summatory a n = ∑ i in finset.Icc 1 n, a i :=
by simp only [summatory, nat.floor_coe]

lemma summatory_eq_floor (x : ℝ) :
  summatory a x = summatory a ⌊x⌋₊ :=
by rw [summatory, summatory, nat.floor_coe]

lemma summatory_eq_of_Ico {n : ℕ} {x : ℝ}
  (hx : x ∈ Ico (n : ℝ) (n + 1)) :
  summatory a x = summatory a n :=
by rw [summatory_eq_floor, nat.floor_eq_on_Ico' _ _ hx]

lemma summatory_eq_of_lt_one {x : ℝ} (hx : x < 1) :
  summatory a x = 0 :=
begin
  rw [summatory, finset.Icc_eq_empty_of_lt, finset.sum_empty],
  rwa [nat.floor_lt' one_ne_zero, nat.cast_one],
end

@[simp] lemma summatory_zero : summatory a 0 = 0 :=
summatory_eq_of_lt_one _ zero_lt_one

@[simp] lemma summatory_one : summatory a 1 = a 1 :=
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

lemma summatory_const_one {x : ℝ} :
  summatory (λ _, (1 : ℝ)) x = (⌊x⌋₊ : ℝ) :=
by { rw [summatory, finset.sum_const, nat.card_Icc, nat.smul_one_eq_coe], refl }

lemma summatory_nonneg' {M : Type*} [ordered_add_comm_group M] {a : ℕ → M} (x : ℝ)
  (ha : ∀ (i : ℕ), 1 ≤ i → (i : ℝ) ≤ x → 0 ≤ a i) :
  0 ≤ summatory a x :=
begin
  apply finset.sum_nonneg,
  simp only [and_imp, finset.mem_Icc],
  intros i hi₁ hi₂,
  apply ha i hi₁ ((nat.le_floor_iff' (ne_of_gt hi₁)).1 hi₂),
end

lemma summatory_nonneg {M : Type*} [ordered_add_comm_group M] (a : ℕ → M) (x : ℝ)
  (ha : ∀ (i : ℕ), 0 ≤ a i) :
  0 ≤ summatory a x :=
summatory_nonneg' _ (λ i hi₁ _, ha i)

lemma summatory_monotone_of_nonneg {M : Type*} [ordered_add_comm_group M] (a : ℕ → M)
  (ha : ∀ (i : ℕ), 0 ≤ a i) :
  monotone (summatory a) :=
begin
  intros i j h,
  refine finset.sum_le_sum_of_subset_of_nonneg _ (λ k _ _, ha _),
  apply finset.Icc_subset_Icc le_rfl (nat.floor_mono h),
end

lemma abs_summatory_bound {M : Type*} [semi_normed_group M] (a : ℕ → M) (k : ℕ)
  {x : ℝ} (hx : x ≤ k) :
  ∥summatory a x∥ ≤ ∑ i in finset.Icc 1 k, ∥a i∥ :=
(abs_summatory_le_sum a).trans
  (finset.sum_le_sum_of_subset_of_nonneg
    (finset.Icc_subset_Icc le_rfl (le_floor_of_le hx)) (by simp))

open measure_theory

@[measurability] lemma measurable_summatory {M : Type*} [add_comm_monoid M] [measurable_space M]
  {a : ℕ → M} :
  measurable (summatory a) :=
begin
  change measurable ((λ y, ∑ i in finset.Icc 1 y, a i) ∘ _),
  exact measurable_from_nat.comp nat.measurable_floor,
end

lemma partial_summation_integrable {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) {f : ℝ → 𝕜} {x y : ℝ}
  (hf' : integrable_on f (Icc x y)) :
  integrable_on (summatory a * f) (Icc x y) :=
begin
  let b := ∑ i in finset.Icc 1 ⌈y⌉₊, ∥a i∥,
  have : integrable_on (b • f) (Icc x y) := integrable.smul b hf',
  refine this.integrable.mono (measurable_summatory.ae_measurable.mul' hf'.1) _,
  rw ae_restrict_iff' (measurable_set_Icc : measurable_set (Icc x _)),
  refine eventually_of_forall (λ z hz, _),
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

-- TODO: Move to mathlib
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

-- TODO: Move to mathlib
lemma integral_rpow_Ioi {a r : ℝ} (hr : r < -1) (ha : 0 < a) :
  ∫ x in Ioi a, x ^ r = - a ^ (r + 1) / (r + 1) :=
tendsto_nhds_unique
  (interval_integral_tendsto_integral_Ioi _ (integrable_on_rpow_Ioi hr ha) tendsto_id)
  (integral_Ioi_rpow_tendsto_aux hr ha tendsto_id)

-- TODO: Move to mathlib
lemma integrable_on_rpow_inv_Ioi {a r : ℝ} (hr : 1 < r) (ha : 0 < a) :
  integrable_on (λ x, (x ^ r)⁻¹) (Ioi a) :=
(integrable_on_rpow_Ioi (neg_lt_neg hr) ha).congr_fun (λ x hx, rpow_neg (ha.trans hx).le _)
  measurable_set_Ioi

-- TODO: Move to mathlib
lemma integral_rpow_inv {a r : ℝ} (hr : 1 < r) (ha : 0 < a) :
  ∫ x in Ioi a, (x ^ r)⁻¹ = a ^ (1 - r) / (r - 1) :=
begin
  rw [←set_integral_congr, integral_rpow_Ioi (neg_lt_neg hr) ha, neg_div, ←div_neg, neg_add',
    neg_neg, neg_add_eq_sub],
  { apply measurable_set_Ioi },
  exact λ x hx, (rpow_neg (ha.trans hx).le _)
end

-- TODO: Move to mathlib
lemma integrable_on_zpow_Ioi {a : ℝ} {n : ℤ} (hn : n < -1) (ha : 0 < a) :
  integrable_on (λ x, x ^ n) (Ioi a) :=
by exact_mod_cast integrable_on_rpow_Ioi (show (n : ℝ) < -1, by exact_mod_cast hn) ha

-- TODO: Move to mathlib
lemma integral_zpow_Ioi {a : ℝ} {n : ℤ} (hn : n < -1) (ha : 0 < a) :
  ∫ x in Ioi a, x ^ n = - a ^ (n + 1) / (n + 1) :=
by exact_mod_cast integral_rpow_Ioi (show (n : ℝ) < -1, by exact_mod_cast hn) ha

-- TODO: Move to mathlib
lemma integrable_on_zpow_inv_Ioi {a : ℝ} {n : ℤ} (hn : 1 < n) (ha : 0 < a) :
  integrable_on (λ x, (x ^ n)⁻¹) (Ioi a) :=
(integrable_on_zpow_Ioi (neg_lt_neg hn) ha).congr_fun (by simp) measurable_set_Ioi

-- TODO: Move to mathlib
lemma integral_zpow_inv_Ioi {a : ℝ} {n : ℤ} (hn : 1 < n) (ha : 0 < a) :
  ∫ x in Ioi a, (x ^ n)⁻¹ = a ^ (1 - n) / (n - 1) :=
begin
  simp_rw [←zpow_neg₀, integral_zpow_Ioi (neg_lt_neg hn) ha, neg_div, ←div_neg, neg_add',
    int.cast_neg, neg_neg, neg_add_eq_sub],
end

-- TODO: Move to mathlib
lemma integrable_on_pow_inv_Ioi {a : ℝ} {n : ℕ} (hn : 1 < n) (ha : 0 < a) :
  integrable_on (λ x, (x ^ n)⁻¹) (Ioi a) :=
by exact_mod_cast integrable_on_zpow_inv_Ioi (show 1 < (n : ℤ), by exact_mod_cast hn) ha

-- TODO: Move to mathlib
lemma integral_pow_inv_Ioi {a : ℝ} {n : ℕ} (hn : 1 < n) (ha : 0 < a) :
  ∫ x in Ioi a, (x ^ n)⁻¹ = (a ^ (n - 1))⁻¹ / (n - 1) :=
by simp_rw [←zpow_coe_nat, integral_zpow_inv_Ioi (show 1 < (n : ℤ), by exact_mod_cast hn) ha,
  int.cast_coe_nat, ←zpow_neg₀, int.coe_nat_sub hn.le, neg_sub, int.coe_nat_one]

lemma fract_mul_integrable {f : ℝ → ℝ} (s : set ℝ)
  (hf' : integrable_on f s) :
  integrable_on (int.fract * f) s :=
begin
  refine integrable.mono hf' _ (eventually_of_forall _),
  { exact measurable_fract.ae_measurable.mul' hf'.1 },
  intro x,
  simp only [normed_field.norm_mul, pi.mul_apply, norm_of_nonneg (int.fract_nonneg _)],
  exact mul_le_of_le_one_left (norm_nonneg _) (int.fract_lt_one _).le,
end

lemma euler_mascheroni_convergence_rate :
  is_O_with 1 (λ x : ℝ, 1 - (∫ t in Ioc 1 x, int.fract t * (t^2)⁻¹) - euler_mascheroni)
    (λ x, x⁻¹) at_top :=
begin
  apply is_O_with.of_bound,
  rw eventually_at_top,
  refine ⟨1, λ x (hx : _ ≤ _), _⟩,
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
      exact mul_le_of_le_one_left (inv_nonneg.2 (sq_nonneg _)) (int.fract_lt_one _).le } },
  exact set_integral_nonneg measurable_set_Ioi
    (λ t ht, div_nonneg (int.fract_nonneg _) (sq_nonneg _)),
end

lemma euler_mascheroni_integral_Ioc_convergence :
  tendsto (λ x : ℝ, 1 - ∫ t in Ioc 1 x, int.fract t * (t^2)⁻¹) at_top (𝓝 euler_mascheroni) :=
by simpa using
  (euler_mascheroni_convergence_rate.is_O.trans_tendsto tendsto_inv_at_top_zero).add_const
    euler_mascheroni

lemma euler_mascheroni_interval_integral_convergence :
  tendsto (λ x : ℝ, (1 : ℝ) - ∫ t in 1..x, int.fract t * (t^2)⁻¹) at_top (𝓝 euler_mascheroni) :=
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

lemma nat_floor_eq_int_floor' {α : Type*} [linear_ordered_ring α] [floor_ring α]
  {y : α} (hy : 0 ≤ y) : (⌊y⌋₊ : α) = ⌊y⌋ :=
begin
  rw ←nat_floor_eq_int_floor hy,
  simp
end

lemma harmonic_series_is_O_aux {x : ℝ} (hx : 1 ≤ x) :
  summatory (λ i, (i : ℝ)⁻¹) x - log x - euler_mascheroni =
    (1 - (∫ t in Ioc 1 x, int.fract t * (t^2)⁻¹) - euler_mascheroni) - int.fract x * x⁻¹ :=
begin
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
  rw [summatory_const_one, nat_floor_eq_int_floor' (zero_le_one.trans hx), ←int.self_sub_floor,
    sub_mul, mul_inv_cancel (zero_lt_one.trans_le hx).ne', sub_sub (1 : ℝ), sub_sub_sub_cancel_left,
    sub_sub, sub_sub, sub_right_inj, ←add_assoc, add_left_inj, ←eq_sub_iff_add_eq', ←integral_sub],
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
    rw [summatory_const_one, nat_floor_eq_int_floor' this.le, mul_neg_eq_neg_mul_symm,
      sub_neg_eq_add, ←add_mul, int.fract_add_floor, sq, mul_inv₀, mul_inv_cancel_left₀ this.ne'] },
  rw [set_integral_congr measurable_set_Ioc this, ←interval_integral.integral_of_le hx,
    integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx), div_one],
end

lemma is_O_with_one_fract_mul (f : ℝ → ℝ) :
  is_O_with 1 (λ (x : ℝ), int.fract x * f x) f at_top :=
begin
  apply is_O_with.of_bound (eventually_of_forall _),
  intro x,
  simp only [one_mul, normed_field.norm_mul],
  refine mul_le_of_le_one_left (norm_nonneg _) _,
  rw norm_of_nonneg (int.fract_nonneg _),
  exact (int.fract_lt_one x).le,
end

lemma harmonic_series_is_O_with :
  is_O_with 2 (λ x, summatory (λ i, (i : ℝ)⁻¹) x - log x - euler_mascheroni) (λ x, x⁻¹) at_top :=
begin
  have : is_O_with 1 (λ (x : ℝ), int.fract x * x⁻¹) (λ x, x⁻¹) at_top := is_O_with_one_fract_mul _,
  refine (euler_mascheroni_convergence_rate.sub this).congr' _ _ eventually_eq.rfl,
  { norm_num1 }, -- I seriously need to prove 1 + 1 = 2
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
  have diff : (∀ (i ∈ Ici (1:ℝ)), has_deriv_at log (i⁻¹) i),
  { rintro i (hi : (1:ℝ) ≤ _),
    exact has_deriv_at_log (zero_lt_one.trans_le hi).ne' },
  have cont : continuous_on (λ x : ℝ, x⁻¹) (Ici 1),
  { exact continuous_on_inv₀.mono  (λ x (hx : _ ≤ _), (zero_lt_one.trans_le hx).ne') },
  have ps := partial_summation_cont' (λ _, (1 : ℝ)) _ _ diff cont x,
  simp only [one_mul] at ps,
  simp only [ps, integral_Icc_eq_integral_Ioc],
  clear ps,
  rw [summatory_const_one, nat_floor_eq_int_floor' (zero_le_one.trans hx), ←int.self_sub_fract,
    sub_mul, sub_sub (x * log x), sub_sub_sub_cancel_left, sub_eq_iff_eq_add, add_assoc,
    ←sub_eq_iff_eq_add', ←add_assoc, sub_add_cancel, ←integral_add],
  { rw [←integral_one, interval_integral.integral_of_le hx, set_integral_congr],
    { apply measurable_set_Ioc },
    intros y hy,
    have hy' : 0 < y := zero_lt_one.trans hy.1,
    rw [←add_mul, summatory_const_one, nat_floor_eq_int_floor' hy'.le, int.fract_add_floor,
      mul_inv_cancel hy'.ne'] },
  { apply fract_mul_integrable,
    exact (cont.mono Icc_subset_Ici_self).integrable_on_Icc.mono_set Ioc_subset_Icc_self },
  { apply (partial_summation_integrable _ _).mono_set Ioc_subset_Icc_self,
    exact (cont.mono Icc_subset_Ici_self).integrable_on_Icc },
end

lemma is_o_const_of_tendsto_at_top (f : ℝ → ℝ) (l : filter ℝ) (h : tendsto f l at_top) (c : ℝ) :
  is_o (λ (x : ℝ), c) f l :=
begin
  rw is_o_iff,
  intros ε hε,
  have : ∀ᶠ (x : ℝ) in at_top, ∥c∥ ≤ ε * ∥x∥,
  { filter_upwards [eventually_ge_at_top (∥c∥ * ε⁻¹), eventually_ge_at_top (0:ℝ)],
    intros x hx₁ hx₂,
    rwa [←mul_inv_le_iff hε, norm_of_nonneg hx₂] },
  exact h.eventually this,
end

lemma is_o_one_log (c : ℝ) : is_o (λ (x : ℝ), c) log at_top :=
is_o_const_of_tendsto_at_top _ _ tendsto_log_at_top _

lemma summatory_log {c : ℝ} (hc : 2 < c) :
  is_O_with c (λ x, summatory (λ i, log i) x - (x * log x - x)) (λ x, log x) at_top :=
begin
  have f₁ : is_O_with 1 (λ (x : ℝ), int.fract x * log x) (λ x, log x) at_top :=
    is_O_with_one_fract_mul _,
  have f₂ : is_o (λ (x : ℝ), (1 : ℝ)) log at_top := is_o_one_log _,
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

lemma summatory_mul_floor_eq_summatory_sum_divisors {x y : ℝ}
  (hy : 0 ≤ x) (xy : x ≤ y) (f : ℕ → ℝ) :
  summatory (λ n, f n * ⌊x / n⌋) y = summatory (λ n, ∑ i in n.divisors, f i) x :=
begin
  simp_rw [summatory, ←nat_floor_eq_int_floor' (div_nonneg hy (nat.cast_nonneg _)),
    ←summatory_const_one, summatory, finset.mul_sum, mul_one, finset.sum_sigma'],
  refine finset.sum_bij _ _ _ _ _,
  -- Construct the forward function
  { intros i hi,
    exact ⟨i.1 * i.2, i.1⟩ },
  -- Show it lands in the correct set
  { rintro ⟨i, j⟩ hi,
    simp_rw [finset.mem_sigma, finset.mem_Icc, nat.mem_divisors, dvd_mul_right, true_and, ne.def,
      nat.mul_eq_zero, not_or_distrib, ←ne.def, nat.le_floor_iff hy, nat.cast_mul,
      ←pos_iff_ne_zero, nat.succ_le_iff],
    simp only [finset.mem_Icc, finset.mem_sigma, nat.succ_le_iff,
      nat.le_floor_iff (div_nonneg hy (nat.cast_nonneg _))] at hi,
    refine ⟨⟨mul_pos hi.1.1 hi.2.1, _⟩, hi.1.1, hi.2.1⟩,
    apply (le_div_iff' _).1 hi.2.2,
    exact nat.cast_pos.2 hi.1.1 },
  -- Show it respects the function
  { rintro ⟨i, j⟩,
    simp },
  -- Show it's injective
  { rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h₁ h₂ h,
    dsimp at h,
    simp only [finset.mem_Icc, finset.mem_sigma, nat.succ_le_iff] at h₁ h₂,
    simp only [heq_iff_eq] at h ⊢,
    cases h.2,
    rw mul_right_inj' h₁.1.1.ne' at h,
    exact ⟨h.2, h.1⟩ },
  -- Show it's surjective
  { rintro ⟨i, j⟩ h,
    refine ⟨⟨j, i / j⟩, _⟩,
    simp_rw [finset.mem_sigma, finset.mem_Icc, nat.mem_divisors, nat.le_floor_iff hy,
      nat.succ_le_iff] at h,
    obtain ⟨⟨hij, hx'⟩, ⟨i, rfl⟩, -⟩ := h,
    simp_rw [exists_prop],
    simp only [canonically_ordered_comm_semiring.mul_pos] at hij,
    simp only [finset.mem_Icc, and_true, true_and, eq_self_iff_true, finset.mem_sigma, heq_iff_eq,
      nat.succ_le_iff, hij.1, hij.2, nat.mul_div_right, le_div_iff, nat.le_floor_iff (hy.trans xy),
      nat.le_floor_iff (div_nonneg hy (nat.cast_nonneg _)), nat.cast_pos, ←nat.cast_mul],
    rw [mul_comm] at hx',
    refine ⟨le_trans _ (hx'.trans xy), hx'⟩,
    rw nat.cast_le,
    apply nat.le_mul_of_pos_left hij.2 }
end

namespace nat.arithmetic_function

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

localized "notation `τ` := σ 0" in arithmetic_function

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
  is_O (λ x : ℝ, summatory (λ i, (τ i : ℝ)) x - x * log x - (2 * euler_mascheroni - 1) * x)
    sqrt at_top :=
sorry

-- BM: This might need a lower bound on `n`, maybe just `1 ≤ n` is good enough?
lemma divisor_bound :
  ∃ (g : ℝ → ℝ), is_O g (λ i, 1 / log (log i)) at_top ∧
    ∀ (n : ℕ), (σ 0 n : ℝ) ≤ n ^ g n :=
sorry

-- BM: Might also need a lower bound on `n`?
lemma weak_divisor_bound (ε : ℝ) (hε : 0 < ε) :
  ∃ C, 0 < C ∧ ∀ n, (σ 0 n : ℝ) ≤ C * (n : ℝ)^ε :=
sorry

lemma big_O_divisor_bound (ε : ℝ) (hε : 0 < ε) :
  is_O (λ n, (σ 0 n : ℝ)) (λ n, (n : ℝ)^ε) filter.at_top :=
sorry

-- BM: I have this defined in another branch, coming to mathlib soon
def von_mangoldt : nat.arithmetic_function ℝ := sorry
localized "notation `Λ` := nat.arithmetic_function.von_mangoldt" in arithmetic_function

lemma von_mangoldt_nonneg (n : ℕ) : 0 ≤ Λ n :=
sorry

lemma von_mangoldt_divisor_sum {n : ℕ} :
  ∑ i in n.divisors, Λ i = log n :=
sorry

lemma von_mangoldt_upper {n : ℕ} : Λ n ≤ log n :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp },
  rw ←von_mangoldt_divisor_sum,
  exact finset.single_le_sum (λ i hi, von_mangoldt_nonneg i) (nat.mem_divisors_self _ hn.ne'),
end

lemma von_mangoldt_summatory {x y : ℝ} (hx : 0 ≤ x) (xy : x ≤ y) :
  summatory (λ n, Λ n * ⌊x / n⌋) y = summatory (λ n, log n) x :=
by simp only [summatory_mul_floor_eq_summatory_sum_divisors hx xy, von_mangoldt_divisor_sum]

lemma helpful_floor_identity {x : ℝ} :
  ⌊x⌋ - 2 * ⌊x/2⌋ ≤ 1 :=
begin
  rw [←int.lt_add_one_iff, ←@int.cast_lt ℝ],
  push_cast,
  linarith [int.sub_one_lt_floor (x/2), int.floor_le x],
end

lemma helpful_floor_identity2 {x : ℝ} (hx₁ : 1 ≤ x) (hx₂ : x < 2) :
  ⌊x⌋ - 2 * ⌊x/2⌋ = 1 :=
begin
  have h₁ : ⌊x⌋ = 1,
  { rw [int.floor_eq_iff, int.cast_one],
    exact ⟨hx₁, hx₂⟩ },
  have h₂ : ⌊x/2⌋ = 0,
  { rw [int.floor_eq_iff],
    norm_cast,
    split;
    linarith },
  rw [h₁, h₂],
  simp,
end

lemma helpful_floor_identity3 {x : ℝ} :
  2 * ⌊x/2⌋ ≤ ⌊x⌋ :=
begin
  have h₄ : (2 : ℝ) * ⌊x / 2⌋ - 1 < ⌊x⌋ :=
    lt_of_le_of_lt (sub_le_sub_right ((le_div_iff' (by norm_num1)).1 (int.floor_le _)) _)
      (int.sub_one_lt_floor x),
  norm_cast at h₄,
  rwa ←int.sub_one_lt_iff,
end

def chebyshev_error (x : ℝ) : ℝ :=
  (summatory (λ i, log i) x - (x * log x - x))
    - 2 * (summatory (λ i, log i) (x/2) - (x/2 * log (x/2) - x/2))

lemma von_mangoldt_floor_sum {x : ℝ} (hx₀ : 0 < x) :
  summatory (λ n, Λ n * (⌊x / n⌋ - 2 * ⌊x / n / 2⌋)) x = log 2 * x + chebyshev_error x :=
begin
  rw [chebyshev_error, mul_sub, log_div hx₀.ne' two_ne_zero, mul_sub, ←mul_assoc,
    mul_div_cancel' x two_ne_zero, mul_sub, sub_right_comm (x * log x), ←sub_add _ (_ - _),
    sub_add_eq_add_sub, sub_sub_sub_cancel_right, ←sub_sub, mul_comm x, add_sub_cancel'_right,
    ←von_mangoldt_summatory hx₀.le le_rfl, summatory,
    ←von_mangoldt_summatory (div_nonneg hx₀.le zero_le_two) (half_le_self hx₀.le), summatory,
    summatory, finset.mul_sum, ←finset.sum_sub_distrib, finset.sum_congr rfl],
  intros i hi,
  rw div_right_comm,
  ring,
end

lemma chebyshev_lower_aux {x : ℝ} (hx : 0 < x) :
  chebyshev_error x ≤ summatory Λ x - log 2 * x :=
begin
  rw [le_sub_iff_add_le', ←von_mangoldt_floor_sum hx],
  apply finset.sum_le_sum,
  intros i hi,
  apply mul_le_of_le_one_right (von_mangoldt_nonneg _),
  norm_cast,
  apply helpful_floor_identity,
end

lemma chebyshev_upper_aux {x : ℝ} (hx : 0 < x) :
  summatory Λ x - summatory Λ (x / 2) - log 2 * x ≤ chebyshev_error x :=
begin
  rw [sub_le_iff_le_add', ←von_mangoldt_floor_sum hx, summatory, summatory],
  have : finset.Icc 1 ⌊x/2⌋₊ ⊆ finset.Icc 1 ⌊x⌋₊,
  { exact finset.Icc_subset_Icc le_rfl (nat.floor_mono (half_le_self hx.le)) },
  rw [←finset.sum_sdiff this, add_sub_cancel],
  refine (finset.sum_le_sum _).trans
    (finset.sum_le_sum_of_subset_of_nonneg (finset.sdiff_subset _ _) _),
  { simp_rw [finset.mem_sdiff, finset.mem_Icc, and_imp, not_and, not_le, nat.le_floor_iff hx.le,
      nat.floor_lt (div_nonneg hx.le zero_le_two), nat.succ_le_iff],
    intros i hi₁ hi₂ hi₃,
    replace hi₃ := hi₃ hi₁,
    norm_cast,
    rw [helpful_floor_identity2, int.cast_one, mul_one],
    { refine (one_le_div _).2 hi₂,
      rwa [nat.cast_pos] },
    rwa [div_lt_iff, ←div_lt_iff'],
    { norm_num1 },
    rwa [nat.cast_pos] },
  rintro i - -,
  apply mul_nonneg (von_mangoldt_nonneg _) _,
  rw sub_nonneg,
  norm_cast,
  apply helpful_floor_identity3,
end

lemma chebyshev_error_O :
  is_O chebyshev_error log at_top :=
begin
  have t : (2 : ℝ) < 3 := by norm_num,
  refine (summatory_log t).is_O.sub (is_O.const_mul_left _ _),
  refine ((summatory_log t).is_O.comp_tendsto (tendsto_id.at_top_div_const zero_lt_two)).trans _,
  apply is_O.of_bound 1,
  filter_upwards [eventually_ge_at_top (2 : ℝ)],
  intros x hx,
  rw [function.comp_app, id.def, one_mul, norm_of_nonneg (log_nonneg _),
    norm_of_nonneg (log_nonneg _), log_le_log];
  linarith
end

lemma chebyshev_lower_explicit {c : ℝ} (hc : c < log 2) :
  ∀ᶠ x : ℝ in at_top, c * x ≤ summatory Λ x :=
begin
  have h₁ := (chebyshev_error_O.trans_is_o is_o_log_id_at_top).bound (sub_pos_of_lt hc),
  filter_upwards [eventually_ge_at_top (1 : ℝ), h₁],
  intros x hx₁ hx₂,
  rw [norm_of_nonneg (zero_le_one.trans hx₁), real.norm_eq_abs] at hx₂,
  have := (neg_le_of_abs_le hx₂).trans (chebyshev_lower_aux (zero_lt_one.trans_le hx₁)),
  linarith,
end

lemma chebyshev_lower :
  is_O (λ x, x) (summatory Λ) at_top :=
begin
  rw [is_O_iff],
  refine ⟨(log 2 / 2)⁻¹, _⟩,
  filter_upwards [eventually_ge_at_top (0 : ℝ),
    chebyshev_lower_explicit (half_lt_self (log_pos one_lt_two))],
  intros x hx₁ hx₂,
  rw [mul_comm, ←div_eq_mul_inv, le_div_iff' (div_pos (log_pos one_lt_two) zero_lt_two),
    norm_of_nonneg hx₁, real.norm_eq_abs],
  exact hx₂.trans (le_abs_self _),
end

lemma chebyshev_trivial_upper_nat (n : ℕ) :
  summatory Λ n ≤ n * log n :=
begin
  rw [summatory_nat, ←nsmul_eq_mul],
  apply (finset.sum_le_of_forall_le _ _ (log n) (λ i hi, _)).trans _,
  { apply von_mangoldt_upper.trans,
    simp only [finset.mem_Icc] at hi,
    exact (log_le_log (nat.cast_pos.2 hi.1) (nat.cast_pos.2 (hi.1.trans hi.2))).2
      (nat.cast_le.2 hi.2) },
  simp
end

lemma chebyshev_trivial_upper {x : ℝ} (hx : 1 ≤ x) :
  summatory Λ x ≤ x * log x :=
begin
  have hx₀ : 0 < x := zero_lt_one.trans_le hx,
  rw [summatory_eq_floor],
  apply (chebyshev_trivial_upper_nat _).trans _,
  exact mul_le_mul (nat.floor_le hx₀.le)
    ((log_le_log (by rwa [nat.cast_pos, nat.floor_pos]) hx₀).2 (nat.floor_le hx₀.le))
    (log_nonneg (by rwa [nat.one_le_cast, nat.le_floor_iff hx₀.le, nat.cast_one])) hx₀.le,
end

lemma chebyshev_upper_inductive {c : ℝ} (hc : log 2 < c) :
  ∃ C, 1 ≤ C ∧ ∀ x : ℕ, summatory Λ x ≤ 2 * c * x + C * log C :=
begin
  have h₁ := (chebyshev_error_O.trans_is_o is_o_log_id_at_top).bound (sub_pos_of_lt hc),
  -- Pull out the constant from h₁. I'd like to use `eventually_at_top` but to make sure the
  -- constant is big, I go via `at_top_basis'` instead.
  obtain ⟨C, hC₁, hC : ∀ x, C ≤ x → _ ≤ _ * ∥x∥⟩ := (at_top_basis' 1).mem_iff.1 h₁,
  refine ⟨C, hC₁, _⟩,
  intro n,
  apply nat.strong_induction_on n, clear n,
  intros n ih,
  cases le_or_lt (n : ℝ) C with hn hn,
  -- Do the case n ≤ C first.
  { refine (summatory_monotone_of_nonneg _ von_mangoldt_nonneg hn).trans _,
    refine (chebyshev_trivial_upper hC₁).trans _,
    refine le_add_of_nonneg_left (mul_nonneg _ (nat.cast_nonneg _)),
    exact mul_nonneg zero_le_two ((log_nonneg one_le_two).trans hc.le) },
  have hn' : 0 < n := nat.succ_le_iff.2 (nat.one_le_cast.1 (hC₁.trans hn.le)),
  have h₁ := chebyshev_upper_aux (nat.cast_pos.2 hn'),
  rw [sub_sub, sub_le_iff_le_add] at h₁,
  apply h₁.trans, clear h₁,
  rw [summatory_eq_floor, ←nat.cast_two, nat.floor_div_eq_div, nat.cast_two, ←add_assoc],
  have h₃ := hC _ hn.le,
  rw real.norm_eq_abs at h₃,
  replace h₃ := le_of_abs_le h₃,
  have h₂ := ih (n / 2) (nat.div_lt_self hn' one_lt_two),
  apply (add_le_add_right (add_le_add h₃ h₂) _).trans,
  rw [add_right_comm, ←add_assoc, add_le_add_iff_right, norm_coe_nat, ←add_mul, sub_add_cancel,
    mul_assoc _ c n, two_mul (_ * _), add_le_add_iff_left, mul_assoc, mul_left_comm],
  apply mul_le_mul_of_nonneg_left _ (le_trans (log_nonneg one_le_two) hc.le),
  rw ←le_div_iff' (zero_lt_two : (0 : ℝ) < 2),
  convert nat.cast_div_le,
  simp
end

lemma chebyshev_upper_real {c : ℝ} (hc : 2 * log 2 < c) :
  ∃ C, 1 ≤ C ∧ is_O_with 1 (summatory Λ) (λ x, c * x + C * log C) at_top :=
begin
  have hc' : log 2 < c / 2 := by rwa lt_div_iff' (zero_lt_two : (0 : ℝ) < _),
  obtain ⟨C, hC₁, hC⟩ := chebyshev_upper_inductive hc',
  refine ⟨C, hC₁, _⟩,
  rw [is_O_with_iff, eventually_at_top],
  refine ⟨0, λ x hx, _⟩,
  rw [summatory_eq_floor, norm_of_nonneg (summatory_nonneg _ _ von_mangoldt_nonneg), one_mul,
    real.norm_eq_abs],
  refine (hC ⌊x⌋₊).trans (le_trans _ (le_abs_self _)),
  rw [mul_div_cancel' _ (@two_ne_zero ℝ _ _), add_le_add_iff_right],
  refine mul_le_mul_of_nonneg_left (nat.floor_le hx) _,
  exact (mul_nonneg zero_le_two (log_nonneg one_le_two)).trans hc.le,
end

lemma chebyshev_upper_explicit {c : ℝ} (hc : 2 * log 2 < c) :
  is_O_with c (summatory Λ) (λ x, x) at_top :=
begin
  let c' := log 2 + c/2,
  have hc'₁ : c' < c,
  { rwa [←lt_sub_iff_add_lt, sub_half, lt_div_iff' (@zero_lt_two ℝ _ _)] },
  have hc'₂ : 2 * log 2 < c',
  { rwa [←sub_lt_iff_lt_add', two_mul, add_sub_cancel, lt_div_iff' (@zero_lt_two ℝ _ _)] },
  obtain ⟨C, hC₁, hC⟩ := chebyshev_upper_real hc'₂,
  refine (hC.trans _ zero_le_one).congr_const (one_mul _),
  apply (is_O_with_const_mul_self c' _ _).add_is_o (is_o_const_of_tendsto_at_top _ _ tendsto_id _),
  rwa [real.norm_eq_abs, abs_of_nonneg],
  exact le_trans (mul_nonneg zero_le_two (log_nonneg one_le_two)) hc'₂.le,
end

/--
Given a function `a : ℕ → M` from the naturals into an additive commutative monoid, this expresses
∑ 1 ≤ p ≤ x, a(p) where `p` is prime.
-/
def prime_summatory {M : Type*} [add_comm_monoid M] (a : ℕ → M) (x : ℝ) : M :=
  ∑ n in (finset.Icc 1 ⌊x⌋₊).filter nat.prime, a n
-- BM: equivalently could say it's `summatory (λ n, if (a n).prime then a n else 0) x`

lemma log_reciprocal :
  is_O (λ x, prime_summatory (λ p, log p / p) x - log x) (λ _, (1 : ℝ)) at_top :=
sorry

lemma prime_counting_asymptotic :
  is_O (λ x, prime_summatory (λ _, (1 : ℝ)) x - summatory Λ x / log x)
    (λ x, x / (log x)^2) at_top :=
sorry

lemma prime_reciprocal : ∃ b,
  is_O (λ x, prime_summatory (λ p, (p : ℝ)⁻¹) x - log (log x) - b) (λ x, 1 / log x) at_top :=
sorry

-- BM: I expect there's a nicer way of stating this but this should be good enough for now
lemma mertens_third :
  ∃ c, is_O (λ x, ∏ p in (finset.Icc 1 ⌊x⌋₊), (1 - (p : ℝ)⁻¹)⁻¹ - c * log x)
        (λ _, (1 : ℝ)) at_top :=
sorry

end nat.arithmetic_function
