/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import measure_theory.measure.lebesgue
import number_theory.liouville.residual
import number_theory.liouville.liouville_with
import analysis.p_series

/-!
# Volume of the set of Liouville numbers

In this file we prove that the set of Liouville numbers with exponent (irrationality measure)
strictly greater than two is a set of Lebesuge measure zero, see
`volume_Union_set_of_liouville_with`.

Since this set is a residual set, we show that the filters `residual` and `volume.ae` are disjoint.
These filters correspond to two common notions of genericity on `ℝ`: residual sets and sets of full
measure. The fact that the filters are disjoint means that two mutually exclusive properties can be
“generic” at the same time (in the sense of different “genericity” filters).

## Tags

Liouville number, Lebesgue measure, residual, generic property
-/

open_locale filter big_operators ennreal topological_space nnreal
open filter set metric measure_theory real

lemma set_of_liouville_with_subset_aux :
  {x : ℝ | ∃ p > 2, liouville_with p x} ⊆
    ⋃ m : ℤ, (λ x : ℝ, x + m) ⁻¹' (⋃ n > (0 : ℕ), 
      {x : ℝ | ∃ᶠ b : ℕ in at_top, ∃ a ∈ finset.Icc (0 : ℤ) b,
        |x - (a : ℤ) / b| < 1 / b ^ (2 + 1 / n : ℝ)}) :=
begin
  rintro x ⟨p, hp, hxp⟩,
  rcases exists_nat_one_div_lt (sub_pos.2 hp) with ⟨n, hn⟩,
  rw lt_sub_iff_add_lt' at hn,
  suffices : ∀ y : ℝ, liouville_with p y → y ∈ Ico (0 : ℝ) 1 →
    ∃ᶠ b : ℕ in at_top, ∃ a ∈ finset.Icc (0 : ℤ) b, |y - a / b| < 1 / b ^ (2 + 1 / (n + 1) : ℝ),
  { simp only [mem_Union, mem_preimage],
    have hx : x + ↑(-⌊x⌋) ∈ Ico (0 : ℝ) 1,
    { simp only [int.floor_le, int.lt_floor_add_one, add_neg_lt_iff_le_add', zero_add, and_self,
        mem_Ico, int.cast_neg, le_add_neg_iff_add_le] },
    refine ⟨-⌊x⌋, n + 1, n.succ_pos, this _ (hxp.add_int _) hx⟩ },
  clear hxp x, intros x hxp hx01,
  refine ((hxp.frequently_lt_rpow_neg hn).and_eventually (eventually_ge_at_top 1)).mono _,
  rintro b ⟨⟨a, hne, hlt⟩, hb⟩,
  rw [rpow_neg b.cast_nonneg, ← one_div] at hlt,
  refine ⟨a, _, hlt⟩,
  replace hb : (1 : ℝ) ≤ b, from nat.one_le_cast.2 hb,
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans_le hb,
  replace hlt : |x - a / b| < 1 / b,
  { refine hlt.trans_le (one_div_le_one_div_of_le hb0 _),
    calc (b : ℝ) = b ^ (1 : ℝ) : (rpow_one _).symm
    ... ≤ b ^ (2 + 1 / (n + 1) : ℝ) : rpow_le_rpow_of_exponent_le hb (one_le_two.trans _),
    simpa using n.cast_add_one_pos.le },
  rw [sub_div' _ _ _ hb0.ne', abs_div, abs_of_pos hb0, div_lt_div_right hb0,
    abs_sub_lt_iff, sub_lt_iff_lt_add, sub_lt_iff_lt_add, ← sub_lt_iff_lt_add'] at hlt,
  rw [finset.mem_Icc, ← int.lt_add_one_iff, ← int.lt_add_one_iff, ← neg_lt_iff_pos_add, add_comm,
    ← @int.cast_lt ℝ, ← @int.cast_lt ℝ], push_cast,
  refine ⟨lt_of_le_of_lt _ hlt.1, hlt.2.trans_le _⟩,
  { simp only [mul_nonneg hx01.left b.cast_nonneg, neg_le_sub_iff_le_add, le_add_iff_nonneg_left] },
  { rw [add_le_add_iff_left],
    calc x * b ≤ 1 * b : mul_le_mul_of_nonneg_right hx01.2.le hb0.le
    ... = b : one_mul b }
end

/-- The set of numbers satisfying the Liouville condition with some exponent `p > 2` has Lebesgue
measure zero. -/
@[simp] lemma volume_Union_set_of_liouville_with :
  volume (⋃ (p : ℝ) (hp : 2 < p), {x : ℝ | liouville_with p x}) = 0 :=
begin
  simp only [← set_of_exists],
  refine measure_mono_null set_of_liouville_with_subset_aux _,
  rw measure_Union_null_iff, intro m, rw real.volume_preimage_add_right, clear m,
  refine (measure_bUnion_null_iff $ countable_encodable _).2 (λ n (hn : 1 ≤ n), _),
  generalize hr : (2 + 1 / n : ℝ) = r,
  replace hr : 2 < r, by simp [← hr, zero_lt_one.trans_le hn], clear hn n,
  refine measure_set_of_frequently_eq_zero _,
  simp only [set_of_exists, ← real.dist_eq, ← mem_ball, set_of_mem_eq],
  set B : ℤ → ℕ → set ℝ := λ a b, ball (a / b) (1 / b ^ r),
  have hB : ∀ a b, volume (B a b) = ↑(2 / b ^ r : ℝ≥0),
  { intros a b, simp only [B, real.volume_ball],
    rw [ennreal.of_real, mul_one_div, to_nnreal_div zero_le_two, to_nnreal_bit0 zero_le_one,
      to_nnreal_one, to_nnreal_rpow_of_nonneg (nat.cast_nonneg _), nnreal.to_nnreal_coe_nat] },
  have : ∀ b : ℕ, volume (⋃ a ∈ finset.Icc (0 : ℤ) b, B a b) ≤ (2 * (b ^ (1 - r) + b ^ (-r)) : ℝ≥0),
  { intro b,
    calc volume (⋃ a ∈ finset.Icc (0 : ℤ) b, B a b)
        ≤ ∑ a in finset.Icc (0 : ℤ) b, volume (B a b) : measure_bUnion_finset_le _ _
    ... = ((b + 1) * (2 / b ^ r) : ℝ≥0) :
      by simp only [hB, int.card_Icc, finset.sum_const, nsmul_eq_mul, sub_zero,
        ← int.coe_nat_succ, int.to_nat_coe_nat, ← nat.cast_succ, ennreal.coe_mul, ennreal.coe_nat]
    ... = _ : _,
    have : 1 - r ≠ 0, by linarith,
    rw [ennreal.coe_eq_coe],
    simp [add_mul, div_eq_mul_inv, nnreal.rpow_neg, nnreal.rpow_sub' _ this, mul_add,
      mul_left_comm] },
  refine ne_top_of_le_ne_top (ennreal.tsum_coe_ne_top_iff_summable.2 _)
    (ennreal.tsum_le_tsum this),
  refine (summable.add _ _).mul_left _; simp only [nnreal.summable_rpow]; linarith
end

lemma ae_not_liouville_with : ∀ᵐ x, ∀ p > (2 : ℝ), ¬liouville_with p x :=
by simpa only [ae_iff, not_forall, not_not, set_of_exists]
  using volume_Union_set_of_liouville_with

lemma ae_not_liouville : ∀ᵐ x, ¬liouville x :=
ae_not_liouville_with.mono $ λ x h₁ h₂, h₁ 3 (by norm_num) (h₂.liouville_with 3)

/-- The set of Liouville numbers has Lebesgue measure zero. -/
@[simp] lemma volume_set_of_liouville : volume {x : ℝ | liouville x} = 0 :=
by simpa only [ae_iff, not_not] using ae_not_liouville

/-- The filters `residual ℝ` and `volume.ae` are disjoint. This means that there exists a residual
set of Lebesgue measure zero (e.g., the set of Liouville numbers). -/
lemma real.disjoint_residual_ae : disjoint (residual ℝ) volume.ae :=
disjoint_of_disjoint_of_mem disjoint_compl_right eventually_residual_liouville ae_not_liouville
