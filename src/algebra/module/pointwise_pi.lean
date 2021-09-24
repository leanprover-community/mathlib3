/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import algebra.pointwise
import algebra.module.pi

/-!
# Pointwise actions on sets in Pi types

This file contains lemmas about pointwise actions on sets in Pi types.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication, pi

-/

open_locale pointwise
open set

@[to_additive]
lemma smul_univ_pi {K R : Type*} [has_scalar K R] (ι : Type*) {r : K} (t : ι → set R) :
  r • pi (univ : set ι) t = pi (univ : set ι) (r • t) :=
begin
  ext x,
  simp only [mem_smul_set, mem_univ_pi],
  split; intro h,
  { rcases h with ⟨h_w, h_h_left, rfl⟩,
    simp only [pi.smul_apply],
    intro i,
    refine ⟨h_w i, h_h_left i, rfl⟩, },
  { use (λ i, classical.some (h i)),
    split,
    { exact λ i, (classical.some_spec (h i)).left, },
    { ext i,
      exact (classical.some_spec (h i)).right, }, },
end

lemma smul_pi' {K R : Type*} [group_with_zero K] [mul_action K R] {ι : Type*} {r : K}
  (t : ι → set R) (S : set ι) (hr : r ≠ 0) : r • S.pi t = S.pi (r • t) :=
begin
  ext x,
  simp only [mem_smul_set, mem_pi],
  split; intro h,
  { rcases h with ⟨h_w, h_h_left, rfl⟩,
    simp only [mul_eq_mul_left_iff, pi.smul_apply],
    intros i hi,
    refine ⟨h_w i, h_h_left i hi, rfl⟩, },
  classical,
  { existsi (λ i, if hiS : i ∈ S then classical.some (h i hiS) else r⁻¹ • x i),
    dsimp,
    split,
    { intros i hiS,
      split_ifs,
      exact (classical.some_spec (h i hiS)).left, },
    { ext i,
      rw [pi.smul_apply],
      split_ifs with hiS,
      exact (classical.some_spec (h i hiS)).right,
      rw [smul_smul, mul_inv_cancel hr, one_smul], }, },
end

@[to_additive]
lemma smul_pi {K R : Type*} [group K] [mul_action K R] {ι : Type*} {r : K} (t : ι → set R)
  (S : set ι) : r • S.pi t = S.pi (λ (i : ι), r • t i) :=
begin
  ext x,
  simp only [mem_smul_set, mem_pi],
  split; intro h,
  { rcases h with ⟨h_w, h_h_left, rfl⟩,
    simp only [mul_eq_mul_left_iff, pi.smul_apply],
    intros i hi,
    refine ⟨h_w i, h_h_left i hi, rfl⟩, },
  classical,
  { existsi (λ i, if hiS : i ∈ S then classical.some (h i hiS) else r⁻¹ • x i),
    dsimp,
    split,
    { intros i hiS,
      split_ifs,
      exact (classical.some_spec (h i hiS)).left, },
    { ext i,
      rw [pi.smul_apply],
      split_ifs with hiS,
      exact (classical.some_spec (h i hiS)).right,
      rw [smul_smul, mul_right_inv, one_smul], }, },
end
