/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import algebra.pointwise
import algebra.module.pi

open_locale pointwise
open set

lemma smul_univ_pi {K : Type*} [has_mul K] (ι : Type*) {r : K} (t : ι → set K) :
  r • pi (univ : set ι) t = pi (univ : set ι) (λ (i : ι), r • t i) :=
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

lemma smul_pi' {K : Type*} [group_with_zero K] (ι : Type*) {r : K} (t : ι → set K) (S : set ι)
  (hr : r ≠ 0) : r • S.pi t = S.pi (λ (i : ι), r • t i) :=
begin
  ext x,
  simp only [mem_smul_set, mem_pi],
  split; intro h,
  { rcases h with ⟨h_w, h_h_left, rfl⟩,
    simp only [mul_eq_mul_left_iff, pi.smul_apply],
    intros i hi,
    refine ⟨h_w i, h_h_left i hi, rfl⟩, },
  classical,
  { use (λ i, if hiS : i ∈ S then classical.some (h i hiS) else r⁻¹ * x i),
    split,
    { intros i hiS,
      split_ifs,
      exact (classical.some_spec (h i hiS)).left, },
    { ext i,
      rw [pi.smul_apply, smul_eq_mul],
      split_ifs with hiS,
      exact (classical.some_spec (h i hiS)).right,
      rw mul_inv_cancel_left' hr, }, },
end

lemma smul_pi {K : Type*} [group K] (ι : Type*) {r : K} (t : ι → set K) (S : set ι) :
  r • S.pi t = S.pi (λ (i : ι), r • t i) :=
begin
  ext x,
  simp only [mem_smul_set, mem_pi],
  split; intro h,
  { rcases h with ⟨h_w, h_h_left, rfl⟩,
    simp only [mul_eq_mul_left_iff, pi.smul_apply],
    intros i hi,
    refine ⟨h_w i, h_h_left i hi, rfl⟩, },
  classical,
  { use (λ i, if hiS : i ∈ S then classical.some (h i hiS) else r⁻¹ * x i),
    split,
    { intros i hiS,
      split_ifs,
      exact (classical.some_spec (h i hiS)).left, },
    { ext i,
      rw [pi.smul_apply, smul_eq_mul],
      split_ifs with hiS,
      exact (classical.some_spec (h i hiS)).right,
      rw mul_inv_cancel_left, }, },
end
