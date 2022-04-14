/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import measure_theory.measure.measure_space_def
import measure_theory.integral.interval_integral
import algebra.order.floor
import analysis.special_functions.integrals

/-!
# Comparing sums and integrals

## Summary

It is often the case that error terms in analysis can be computed by converting the
an infinite sum to the improper integral of an antitone function. This file will eventually enable
that.

At the moment it contains one lemma in this direction: `antitone_on.integral_le_sum` which can
be paired with a `filter.tendsto` to estimate some errors. Several more lemmas will be added to the
API to directly address these issues forthwith.

## Main Results

* `antitone_on.integral_le_sum`: The integral of an antitone function is at most the sum of its
  values at integer steps

## Tags

analysis, comparison, asymptotics
-/

open set
open_locale big_operators

lemma antitone_on.integral_le_sum {x₀ : ℝ} {a : ℕ} {f : ℝ → ℝ}
  (hf : antitone_on f (Icc x₀ (x₀ + a))) :
  ∫ x in x₀..(x₀ + a), f x ≤ ∑ i in finset.range a, f (x₀ + i) :=
begin
  have : ∫ x in x₀..(x₀ + a), f x = ∫ x in 0..↑a, f (x₀ + x),
  { simp only [interval_integral.integral_comp_add_left, add_zero], },
  rw this,
  conv
  { to_rhs, congr, skip, funext, rw ←@integral_const_on_unit_interval (x₀ + i) (f (x₀ + i)), },
  have hint : ∀ (k : ℕ), k < a → interval_integrable (λ x, f (x₀ + x))
    real.measure_space.volume k (k + 1),
  { intros k hk,
    apply antitone_on.interval_integrable,
    rw interval_of_le,
    { intros x hx y hy hxy,
      refine hf _ _ (by simp [hxy]),
      { split,
        { rw le_add_iff_nonneg_right, calc (0 : ℝ) ≤ k : by simp ... ≤ x : hx.left, },
        { rw add_le_add_iff_left,
          refine le_trans hx.right _,
          norm_cast,
          exact nat.succ_le_of_lt hk, }, },
      { split,
        { rw le_add_iff_nonneg_right, calc (0 : ℝ) ≤ k : by simp ... ≤ y : hy.left,},
        { rw add_le_add_iff_left,
          refine le_trans hy.right _,
          norm_cast,
          exact nat.succ_le_of_lt hk, }, }, },
    { simp, }, },
  rw [←nat.cast_zero, ←interval_integral.sum_integral_adjacent_intervals hint],
  refine finset.sum_le_sum (λ i hi, _),
  rw finset.mem_range at hi,
  simp only [nat.cast_add, nat.cast_one, interval_integral.integral_comp_add_left,
    interval_integral.integral_const, add_tsub_cancel_left, algebra.id.smul_eq_mul, one_mul],
  rw [←@integral_const_on_unit_interval (x₀ + i) (f (x₀ + i)), add_assoc],
  refine interval_integral.integral_mono_on (by simp) _ (by simp) _,
  { apply antitone_on.interval_integrable,
    rw interval_of_le,
    { intros x hx y hy hxy,
      refine hf ⟨le_trans (by simp) hx.left, le_trans hx.right _⟩
        ⟨le_trans (by simp) hy.left, le_trans hy.right _⟩ hxy,
      { rw add_le_add_iff_left,
        norm_cast,
        exact nat.succ_le_of_lt hi,},
      { rw add_le_add_iff_left,
        norm_cast,
        exact nat.succ_le_of_lt hi, }, },
    { linarith, }, },
  { refine (λ x hx, hf _ _ hx.left),
    exact ⟨by simp, by simp [hi.le]⟩,
    refine ⟨le_trans (by simp) hx.left, le_trans hx.right _⟩,
    rw add_le_add_iff_left,
    norm_cast,
    exact nat.succ_le_of_lt hi, },
end

lemma antitone_on.integral_le_sum_Ico {a b : ℕ} {f : ℝ → ℝ} (hab : a ≤ b)
  (hf : antitone_on f (set.Icc a b)) : ∫ x in a..b, f x ≤ ∑ x in finset.Ico a b, f x :=
begin
  have bb : b = (b - a) + a, { zify, ring, },
  conv { to_rhs, rw [←zero_add a, bb], },
  have bb' : (b : ℝ) = (a : ℝ) + ↑(b - a), { simp [hab], },
  conv { to_lhs, rw bb', },
  rw [←finset.sum_Ico_add, nat.Ico_zero_eq_range],
  conv
  { to_rhs, congr, skip, funext, rw nat.cast_add a x, },
  apply antitone_on.integral_le_sum,
  rwa ←bb',
end
