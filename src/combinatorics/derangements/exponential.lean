/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson, Patrick Massot
-/
import combinatorics.derangements.finite
import analysis.complex.basic
import data.complex.exponential
import topology.metric_space.cau_seq_filter

/-!
# Derangement exponential series

This file proves that the probability of a permutation on n elements being a derangement is 1/e.
The specific lemma is `num_derangements_tendsto_inv_e`.
-/
open filter
open finset

open_locale big_operators
open_locale topological_space

lemma complex.tendsto_iff_real (u : ℕ → ℝ) (x : ℝ) :
  tendsto (λ n, u n) at_top (𝓝 x) ↔
  tendsto (λ n, (u n : ℂ)) at_top (𝓝 (x : ℂ)) :=
  ⟨(complex.continuous_of_real.tendsto x).comp, (complex.continuous_re.tendsto x).comp⟩

lemma complex.tendsto_exp_series (z : ℂ) :
  tendsto (λ n, ∑ k in range n, z^k / k.factorial) at_top (𝓝 z.exp) :=
begin
  convert z.exp'.tendsto_limit,
  unfold complex.exp,
end

lemma real.tendsto_exp_series (x : ℝ) :
  tendsto (λ n, ∑ k in range n, x^k / k.factorial) at_top (𝓝 x.exp) :=
begin
  rw complex.tendsto_iff_real,
  convert complex.tendsto_exp_series x; simp,
end

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
    -- shift the function by 1, and use the power series lemma
    rw tendsto_add_at_top_iff_nat 1,
    exact real.tendsto_exp_series (-1) },
  intro n,
  rw [← int.cast_coe_nat, num_derangements_sum],
  push_cast,
  rw finset.sum_div,
  -- get down to individual terms
  refine finset.sum_congr (refl _) _,
  intros k hk,
  have h_le : k ≤ n := finset.mem_range_succ_iff.mp hk,
  rw [nat.asc_factorial_eq_div, nat.add_sub_cancel' h_le],
  push_cast [nat.factorial_dvd_factorial h_le],
  field_simp [nat.factorial_ne_zero],
  ring,
end
