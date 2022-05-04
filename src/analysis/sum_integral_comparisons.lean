/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import measure_theory.measure.measure_space_def
import measure_theory.integral.interval_integral
import algebra.order.floor
import data.set.function
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

open set measure_theory.measure_space
open_locale big_operators

lemma antitone.monotone_of_neg_arg { f : ℝ → ℝ } (hf : antitone f) :
  monotone (λ x, f (-x)) :=
(λ x y hxy, hf (neg_le_neg_iff.mpr hxy))

lemma antitone.monotone_of_neg { f : ℝ → ℝ } (hf : antitone f) :
  monotone (λ x, -(f x)) :=
(λ x y hxy, neg_le_neg_iff.mpr (hf hxy))

lemma antitone_on.monotone_on_of_neg_arg { f : ℝ → ℝ } {s : set ℝ} (hf : antitone_on f s) :
  monotone_on (λ x, f (-x)) (-s) :=
(λ x hx y hy hxy, hf (mem_neg.mp hy) (mem_neg.mp hx) (neg_le_neg_iff.mpr hxy))

lemma antitone_on.monotone_on_of_neg { f : ℝ → ℝ } {s : set ℝ} (hf : antitone_on f s) :
  monotone_on (λ x, -(f x)) s :=
(λ x hx y hy hxy, neg_le_neg_iff.mpr (hf hx hy hxy))

lemma monotone.antitone_of_neg_arg { f : ℝ → ℝ } (hf : monotone f) :
  antitone (λ x, f (-x)) :=
(λ x y hxy, hf (neg_le_neg_iff.mpr hxy))

lemma monotone.antitone_of_neg { f : ℝ → ℝ } (hf : monotone f) :
  antitone (λ x, -(f x)) :=
(λ x y hxy, neg_le_neg_iff.mpr (hf hxy))

lemma monotone_on.antitone_on_of_neg_arg { f : ℝ → ℝ } {s : set ℝ} (hf : monotone_on f s) :
  antitone_on (λ x, f (-x)) (-s) :=
(λ x hx y hy hxy, hf (mem_neg.mp hy) (mem_neg.mp hx) (neg_le_neg_iff.mpr hxy))

lemma monotone_on.antitone_on_of_neg { f : ℝ → ℝ } {s : set ℝ} (hf : monotone_on f s) :
  antitone_on (λ x, -(f x)) s :=
(λ x hx y hy hxy, neg_le_neg_iff.mpr (hf hx hy hxy))

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

private lemma sub_comm {a b : ℝ} : -a - b = -b - a := by ring

private lemma finset.sum_bij_on
  {f : ℕ → ℝ} {g : ℕ → ℕ} {s t : finset ℕ} (hg : set.bij_on g t s) :
  ∑ i in t, f (g i) = ∑ i in s, f i :=
begin
  rw [←finsum_mem_coe_finset, ←finsum_mem_coe_finset],
  exact finsum_mem_eq_of_bij_on g hg (λ _ _, rfl),
end

lemma antitone_on.sum_le_integral {x₀ : ℝ} {a : ℕ} {f : ℝ → ℝ}
  (hf : antitone_on f (Icc x₀ (x₀ + a))) :
  ∑ i in finset.range a, f (x₀ + i + 1) ≤ ∫ x in x₀..(x₀ + a), f x :=
begin
  have hneg : -(set.Icc x₀ (x₀ + a)) = set.Icc ((-x₀ - a)) ((-x₀ - a) + a) , {
    simp only [set.has_involutive_neg, preimage_neg_Icc, neg_add_rev, sub_add_cancel],
    have : -↑a + -x₀ = -x₀ - a, ring,
    rw this,
  },
  have := hf.monotone_on_of_neg_arg.antitone_on_of_neg,
  rw hneg at this,
  have := this.integral_le_sum,
  conv at this
  { congr, congr, simp only,
    skip, rw sub_comm,
    skip, skip, skip, congr, skip, simp only, },
  rw [interval_integral.integral_neg, finset.sum_neg_distrib, neg_le_neg_iff,
    interval_integral.integral_comp_neg] at this,
  simp only [neg_add_rev, neg_sub, sub_neg_eq_add, sub_add_cancel, neg_neg] at this,
  have : set.bij_on (λ i : ℕ, a - 1 - i) (finset.range a) (finset.range a),
  { split,
    { intros x hx,
      simp only [finset.mem_coe, finset.mem_range] at hx ⊢,
      have : 0 < a, calc 0 ≤ x : by simp ... < a : hx,
      calc a - 1 - x ≤ a - 1 : by simp ... < a : nat.pred_lt (zero_lt_iff.mp this), },
    split,
    { intros x hx y hy hxy,
      simp only [finset.mem_coe, finset.mem_range] at hx hy hxy,
      rw [tsub_tsub a 1 x, tsub_tsub a 1 y] at hxy,
      -- Prep for zify
      have : 1 + x ≤ a, { rw add_comm 1 x, exact nat.succ_le_iff.mp hx, },
      have : 1 + y ≤ a, { rw add_comm 1 y, exact nat.succ_le_iff.mp hy, },
      zify at ⊢ hxy,
      linarith [hxy], },
    { refine λ x hx, ⟨a - 1 - x, _⟩,
      simp only [finset.mem_coe, finset.mem_range] at hx ⊢,
      split,
      { have : 0 < a, calc 0 ≤ x : by simp ... < a : hx,
        calc a - 1 - x ≤ a - 1 : by simp ... < a : nat.pred_lt (zero_lt_iff.mp this), },
      { -- This section of the proof is trying to turn a lot of ℕ-subtraction into ℤ-subtraction
        -- so we can just invoke `ring`. To do so, we need to provide assumptions that various
        -- terms are `≤` other terms, but _in the right order_. This is extremely odd and likely
        -- brittle.
        have : a - 1 - x ≤ a - 1, simp,
        have := calc 0 ≤ x : by simp ... < a : hx,
        have : 1 ≤ a, exact nat.one_le_iff_ne_zero.mpr (zero_lt_iff.mp this),
        zify,
        rw tsub_tsub a 1 x,
        have : 1 + x ≤ a, { rw add_comm 1 x, exact nat.succ_le_iff.mp hx, },
        zify,
        ring_nf,
        have : ↑(1 + x) = (1 : ℤ) + ↑x, simp,
        rw this,
        ring, }, }, },
  have : ∑ (x : ℕ) in finset.range a, f (-↑x + (↑a + x₀)) =
    ∑ (i : ℕ) in finset.range a, f (x₀ + ↑i + 1),
  { rw ←finset.sum_bij_on this,
    refine finset.sum_congr rfl _,
    intros x hx,
    congr' 1,
    simp only [finset.mem_coe, finset.mem_range] at hx ⊢,
    rw tsub_tsub a 1 x,
    have : 1 + x ≤ a, { rw add_comm 1 x, exact nat.succ_le_iff.mp hx, },
    simp only [this, nat.cast_sub, nat.cast_add, nat.cast_one, neg_sub],
    ring, },
  rwa ←this,
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
