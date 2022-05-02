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

It is often the case that error terms in analysis can be computed by comparing
an infinite sum to the improper integral of an antitone function. This file will eventually enable
that.

At the moment it contains two lemmas in this direction: `antitone_on.integral_le_sum` and
`antitone_on.sum_le_integral` which can be paired with a `filter.tendsto` to estimate some errors.

`TODO`: Add more lemmas to the API to directly address limiting issues

## Main Results

* `antitone_on.integral_le_sum`: The integral of an antitone function is at most the sum of its
  values at integer steps aligning with the left-hand side of the interval
* `antitone_on.sum_le_integral`: The sum of an antitone function along integer steps aligning with
  the right-hand side of the interval is at most the integral of the function along that interval

## Tags

analysis, comparison, asymptotics
-/

open set
open_locale big_operators

lemma antitone_on.integral_le_sum {x₀ : ℝ} {a : ℕ} {f : ℝ → ℝ}
  (hf : antitone_on f (Icc x₀ (x₀ + a))) :
  ∫ x in x₀..(x₀ + a), f x ≤ ∑ i in finset.range a, f (x₀ + i) :=
begin
  have hint : ∀ (k : ℕ), k < a → interval_integrable f volume (x₀+k) (x₀ + (k + 1 : ℕ)),
  { assume k hk,
    refine (hf.mono _).interval_integrable,
    rw interval_of_le,
    { apply Icc_subset_Icc,
      { simp only [le_add_iff_nonneg_right, nat.cast_nonneg] },
      { simp only [add_le_add_iff_left, nat.cast_le, nat.succ_le_of_lt hk] } },
    { simp only [add_le_add_iff_left, nat.cast_le, nat.le_succ] } },
  calc
  ∫ x in x₀..(x₀ + a), f x = ∑ i in finset.range a, ∫ x in (x₀+i)..(x₀+(i+1 : ℕ)), f x :
    begin
      convert (interval_integral.sum_integral_adjacent_intervals hint).symm,
      simp only [nat.cast_zero, add_zero],
    end
  ... ≤ ∑ i in finset.range a, ∫ x in (x₀+i)..(x₀+(i+1)), f (x₀ + i) :
    begin
      apply finset.sum_le_sum (λ i hi, _),
      have ia : i < a := finset.mem_range.1 hi,
      refine interval_integral.integral_mono_on (by simp) (hint _ ia) (by simp) (λ x hx, _),
      apply hf _ _ hx.1,
      { simp only [ia.le, mem_Icc, le_add_iff_nonneg_right, nat.cast_nonneg, add_le_add_iff_left,
          nat.cast_le, and_self] },
      { refine mem_Icc.2 ⟨le_trans (by simp) hx.1, le_trans hx.2 _⟩,
        simp only [add_le_add_iff_left, nat.cast_le, nat.succ_le_of_lt ia] },
    end
  ... = ∑ i in finset.range a, f (x₀ + i) : by simp
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

lemma antitone_on.sum_le_integral
  {x₀ : ℝ} {a : ℕ} {f : ℝ → ℝ}
  (hf : antitone_on f (Icc x₀ (x₀ + a))) :
  ∑ i in finset.range a, f (x₀ + i + 1) ≤ ∫ x in x₀..(x₀ + a), f x :=
begin
  have : ∫ x in x₀..(x₀ + a), f x = ∫ x in 0..↑a, f (x₀ + x),
  { simp only [interval_integral.integral_comp_add_left, add_zero], },
  rw this,
  conv
  { to_lhs, congr, skip, funext, rw ←@integral_const_on_unit_interval (x₀ + i) (f (x₀ + i + 1)), },
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
    { linarith, }, },
  rw [←nat.cast_zero, ←interval_integral.sum_integral_adjacent_intervals hint],
  refine finset.sum_le_sum (λ i hi, _),
  rw finset.mem_range at hi,
  simp only [interval_integral.integral_const, add_tsub_cancel_left, algebra.id.smul_eq_mul,
    one_mul, nat.cast_add, nat.cast_one, interval_integral.integral_comp_add_left],
  rw [←@integral_const_on_unit_interval (x₀ + i) (f (x₀ + i + 1)), add_assoc],
  refine interval_integral.integral_mono_on (by simp) (by simp) _ _,
  apply antitone_on.interval_integrable,
  rw interval_of_le,
  { intros x hx y hy hxy,
    refine hf _ _ (by simp [hxy]),
    { split,
      { exact le_trans (by simp) hx.left, },
      { refine le_trans hx.right _,
        rw add_le_add_iff_left,
        norm_cast,
        exact nat.succ_le_of_lt hi, }, },
    { split,
      { exact le_trans (by simp) hy.left, },
      { refine le_trans hy.right _,
        rw add_le_add_iff_left,
        norm_cast,
        exact nat.succ_le_of_lt hi, }, }, },
  { simp, },
  { intros x hx,
    refine hf _ _ hx.right,
    { refine ⟨le_trans (by simp) hx.left, le_trans hx.right _⟩,
      rw add_le_add_iff_left,
      norm_cast,
      exact nat.succ_le_of_lt hi, },
    { refine ⟨by { rw le_add_iff_nonneg_right, norm_cast, simp, }, _⟩,
      rw add_le_add_iff_left,
      norm_cast,
      exact nat.succ_le_of_lt hi, }, },
end

lemma antitone_on.sum_le_integral_Ico {a b : ℕ} {f : ℝ → ℝ} (hab : a ≤ b)
  (hf : antitone_on f (set.Icc a b)) :
  ∑ i in finset.Ico a b, f (i + 1) ≤ ∫ x in a..b, f x :=
begin
  have bb : b = (b - a) + a, { zify, ring, },
  conv { to_lhs, rw [←zero_add a, bb], },
  have bb' : (b : ℝ) = (a : ℝ) + ↑(b - a), { simp [hab], },
  conv { to_rhs, rw bb', },
  rw [←finset.sum_Ico_add, nat.Ico_zero_eq_range],
  conv
  { to_lhs, congr, skip, funext, rw nat.cast_add a x, },
  apply antitone_on.sum_le_integral,
  rwa ←bb',
end
