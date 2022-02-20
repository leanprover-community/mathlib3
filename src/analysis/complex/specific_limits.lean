/-
Copyright (c) 2022 Dylan MacKenzie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dylan MacKenzie
-/

import analysis.complex.basic
import analysis.normed.group.infinite_sum
import analysis.specific_limits

/-!
# A collection of specific limit computations involving complex numbers
-/

open filter finset asymptotics
open_locale nat topological_space big_operators

section is_R_or_C

variables {E : Type*} [is_R_or_C E]
variables {x : ℝ} {f : ℕ → ℝ} {z : ℕ → E}

/-- **Dirichlet's Test** for monotone sequences. -/
theorem cauchy_seq_series_mul_of_monotone_tendsto_zero_of_series_bounded
  (hfa : monotone f) (hf0 : tendsto f at_top (𝓝 0)) (hgx : ∀ n, ∥∑ i in range n, z i∥ ≤ x) :
  cauchy_seq (λ n, ∑ i in range (n+1), ↑(f i) * z i) :=
begin
  simp_rw [sum_range_by_parts _ _ (nat.succ_pos _), sub_eq_add_neg,
           nat.succ_sub_succ_eq_sub, tsub_zero],
  apply cauchy_seq.add _ _,
  { exact normed_uniform_group },
  { convert tendsto.cauchy_seq (normed_field.tendsto_zero_smul_of_tendsto_zero_of_bounded hf0
    ⟨x, eventually_map.mpr (eventually_of_forall (λ n, hgx (n+1)))⟩),
    funext,
    simp_rw [←smul_eq_mul, pi.smul_apply', algebra.smul_def],
    refl },
  apply cauchy_seq.neg (cauchy_seq_range_of_norm_bounded _ _ (_ : ∀ n, _ ≤ x * |f(n+1) - f(n)|)),
  { exact normed_uniform_group },
  { conv in (|_|) { rw abs_of_nonneg (sub_nonneg_of_le (hfa (nat.le_succ _))) },
    simp_rw ←mul_sum,
    apply uniform_continuous.comp_cauchy_seq real.uniform_continuous_mul_const _,
    simp_rw [sum_range_sub, sub_eq_add_neg],
    exact cauchy_seq.add_const (tendsto.cauchy_seq hf0) },
  { intro n,
    rw normed_field.norm_mul,
    norm_cast,
    rw real.norm_eq_abs,
    exact decidable.mul_le_mul_of_nonneg_right (hgx (n+1)) (abs_nonneg _) },
end

/-- **Dirichlet's test** for antitone sequences. -/
theorem cauchy_seq_series_mul_of_antitone_tendsto_zero_of_series_bounded
  (hfa : antitone f) (hf0 : tendsto f at_top (𝓝 0)) (hzx : ∀ n, ∥∑ i in range n, z i∥ ≤ x) :
  cauchy_seq (λ n, ∑ i in range (n+1), ↑(f i) * z i) :=
begin
  have hfa': monotone (λ x, -f x) := λ _ _ hab, neg_le_neg $ hfa hab,
  have hf0': tendsto (λ x, -f x) at_top (𝓝 0) := by { convert filter.tendsto.neg hf0, norm_num },
  convert cauchy_seq.neg
    (cauchy_seq_series_mul_of_monotone_tendsto_zero_of_series_bounded hfa' hf0' hzx),
  funext,
  simp only [sum_neg_distrib, neg_mul, pi.neg_apply, neg_neg, is_R_or_C.of_real_neg],
end

private lemma norm_sum_neg_one_pow_le (n : ℕ) : ∥∑ i in range n, (-1 : ℝ) ^ i∥ ≤ 1 :=
by { rw [←geom_sum_def, neg_one_geom_sum], split_ifs; norm_num }

/-- The **alternating series test** for monotone sequences. -/
theorem cauchy_seq_alternating_series_of_monotone_tendsto_zero
  (hfa : monotone f) (hf0 : tendsto f at_top (𝓝 0)) :
  cauchy_seq (λ n, ∑ i in range (n+1), f i * (-1) ^ i) :=
cauchy_seq_series_mul_of_monotone_tendsto_zero_of_series_bounded hfa hf0 norm_sum_neg_one_pow_le

/-- The **alternating series test** for antitone sequences. -/
theorem cauchy_seq_alternating_series_of_antitone_tendsto_zero
  (hfa : antitone f) (hf0 : tendsto f at_top (𝓝 0)) :
  cauchy_seq (λ n, ∑ i in range (n+1), f i * (-1) ^ i) :=
cauchy_seq_series_mul_of_antitone_tendsto_zero_of_series_bounded hfa hf0 norm_sum_neg_one_pow_le

end is_R_or_C
