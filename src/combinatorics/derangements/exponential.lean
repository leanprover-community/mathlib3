/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson, Patrick Massot
-/
import analysis.special_functions.exponential
import combinatorics.derangements.finite
import order.filter.basic

/-!
# Derangement exponential series

This file proves that the probability of a permutation on n elements being a derangement is 1/e.
The specific lemma is `num_derangements_tendsto_inv_e`.
-/
open filter

open_locale big_operators
open_locale topological_space

theorem num_derangements_tendsto_inv_e :
  tendsto (λ n, (num_derangements n : ℝ) / n.factorial) at_top
  (𝓝 (real.exp (-1))) :=
begin
  -- we show that d(n)/n! is the partial sum of exp(-1), but offset by 1.
  -- this isn't entirely obvious, since we have to ensure that asc_factorial and
  -- factorial interact in the right way, e.g., that k ≤ n always
  let s : ℕ → ℝ := λ n, ∑ k in finset.range n, (-1 : ℝ)^k / k.factorial,
  suffices : ∀ n : ℕ, (num_derangements n : ℝ) / n.factorial = s(n+1),
  { simp_rw this,
    -- shift the function by 1, and then use the fact that the partial sums
    -- converge to the infinite sum
    rw tendsto_add_at_top_iff_nat 1,
    apply has_sum.tendsto_sum_nat,
    -- there's no specific lemma for ℝ that ∑ x^k/k! sums to exp(x), but it's
    -- true in more general fields, so use that lemma
    rw real.exp_eq_exp_ℝ_ℝ,
    exact exp_series_field_has_sum_exp (-1 : ℝ) },
  intro n,
  rw [← int.cast_coe_nat, num_derangements_sum],
  push_cast,
  rw finset.sum_div,
  -- get down to individual terms
  refine finset.sum_congr (refl _) _,
  intros k hk,
  have h_le : k ≤ n := finset.mem_range_succ_iff.mp hk,
  rw [nat.asc_factorial_eq_div, add_tsub_cancel_of_le h_le],
  push_cast [nat.factorial_dvd_factorial h_le],
  field_simp [nat.factorial_ne_zero],
  ring,
end
