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

* `antitone_on.integral_le_sum`: The integral of an antitone function is at most the sum of its values
  integer points (left hand side)

## Tags

analysis, comparison, asymptotics
-/

open_locale big_operators

lemma convert_finite_sum_to_interval_integral {m n : ℕ} {f : ℝ → ℝ} (hmn : m ≤ n) :
  ∑ (i : ℕ) in finset.Ico m n, ∫ (x : ℝ) in ↑i..↑i + 1, f ↑i =
  ∫ (x : ℝ) in m..n, f ↑⌊x⌋₊ :=
begin
  conv
  { to_lhs, congr, skip, funext, rw integral_const_on_unit_interval, },
  obtain ⟨n', hn'⟩ := le_iff_exists_add.mp hmn,
  rw [hn', ←interval_integral.sum_integral_adjacent_intervals'],
  { apply finset.sum_congr rfl,
    intros x hx,
    rw ← @integral_const_on_unit_interval x (f ↑x),
    apply interval_integral.integral_congr_ae,
    rw [set.interval_oc_of_le (calc (x : ℝ) ≤ x + 1 : by simp), measure_theory.ae_iff],
    refine real.measure_space.volume.to_outer_measure.mono_null _
      (@real.volume_singleton ((x : ℝ) + 1)),
    simp only [set.mem_Ioc, and_imp, not_forall, exists_prop, set.subset_singleton_iff,
      set.mem_set_of_eq],
    intros y hy hy' hf,
    cases lt_or_eq_of_le hy',
    { exfalso, rw nat.floor_eq_on_Ico x y ⟨le_of_lt hy, h⟩ at hf, exact hf rfl, },
    { exact h, }, },
  { intros k hk,
    rw [interval_integrable_iff, set.interval_oc_of_le (calc (k : ℝ) ≤ ↑(k + 1) : by simp)],
    have : measure_theory.integrable_on (λ x : ℝ, f ↑k) (set.Ioc (k : ℝ) (↑k + 1))
      real.measure_space.volume,
    { simp, },
    apply this.congr_fun',
    rw [filter.eventually_eq, measure_theory.ae_iff],
    simp only [measure_theory.measure.restrict_apply', measurable_set_Ioc],
    refine measure_theory.outer_measure.mono_null _ _ (@real.volume_singleton ((k : ℝ) + 1)),
    simp only [set.subset_singleton_iff, set.mem_inter_eq, set.mem_set_of_eq, set.mem_Ioc, and_imp],
    intros y hf hy hy',
    cases lt_or_eq_of_le hy',
    { exfalso, rw k.floor_eq_on_Ico y ⟨le_of_lt hy, h⟩ at hf, exact hf rfl, },
    { exact h, }, },
end

lemma antitone_on.integral_le_sum {a b : ℕ} {f : ℝ → ℝ} (hab : a ≤ b)
  (hf : antitone_on f (set.Icc a b)) : ∫ x in a..b, f x ≤ ∑ x in finset.Ico a b, f x :=
begin
  have : ∀ (x : ℝ), x ∈ set.Icc (a : ℝ) ↑b → f x ≤ f ⌊x⌋₊,
  { intros x hx,
    apply hf (nat.floor_mem_Icc_of_mem_Icc hx) hx,
    exact nat.floor_le (calc (0 : ℝ) ≤ ↑a : by simp ... ≤ x : hx.left), },
  transitivity,
  refine interval_integral.integral_mono_on (nat.cast_le.mpr hab) _ _ this,
  apply antitone_on.interval_integrable,
  rwa set.interval_of_le (calc (a : ℝ) ≤ b : nat.cast_le.mpr hab),
  apply antitone_on.interval_integrable,
  rwa set.interval_of_le (calc (a : ℝ) ≤ b : nat.cast_le.mpr hab),
  intros c hc d hd hcd,
  exact hf (nat.floor_mem_Icc_of_mem_Icc hc) (nat.floor_mem_Icc_of_mem_Icc hd)
    (nat.cast_le.mpr $ nat.floor_mono hcd),
  conv
  { to_rhs, congr, skip, funext, rw ← @integral_const_on_unit_interval x (f ↑x), },
  rw convert_finite_sum_to_interval_integral hab,
end
