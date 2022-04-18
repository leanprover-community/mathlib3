/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.normed_space.basic
import analysis.normed_space.pi_Lp
import analysis.inner_product_space.pi_L2

/-!
# Matrices as a normed space

In this file we provide the following non-instances on matrices, using the elementwise norm:

* `matrix.semi_normed_group`
* `matrix.normed_group`
* `matrix.normed_space`

These are not declared as instances because there are several natural choices for defining the norm
of a matrix.
-/

noncomputable theory

namespace matrix

variables {R l m n α : Type*} [fintype l] [fintype m] [fintype n]

section semi_normed_group
variables [semi_normed_group α]

/-- Seminormed group instance (using sup norm of sup norm) for matrices over a seminormed ring. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def semi_normed_group : semi_normed_group (matrix m n α) :=
pi.semi_normed_group

local attribute [instance] matrix.semi_normed_group

lemma norm_le_iff {r : ℝ} (hr : 0 ≤ r) {A : matrix m n α} :
  ∥A∥ ≤ r ↔ ∀ i j, ∥A i j∥ ≤ r :=
by simp [pi_norm_le_iff hr]

lemma norm_lt_iff {r : ℝ} (hr : 0 < r) {A : matrix m n α} :
  ∥A∥ < r ↔ ∀ i j, ∥A i j∥ < r :=
by simp [pi_norm_lt_iff hr]

lemma norm_entry_le_entrywise_sup_norm (A : matrix m n α) {i : m} {j : n} :
  ∥A i j∥ ≤ ∥A∥ :=
(norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

end semi_normed_group

/-- Normed group instance (using sup norm of sup norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normed_group [normed_group α] : normed_group (matrix m n α) :=
pi.normed_group


section normed_space
local attribute [instance] matrix.semi_normed_group

variables [normed_field R] [semi_normed_group α] [normed_space R α]

/-- Normed space instance (using sup norm of sup norm) for matrices over a normed field.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normed_space : normed_space R (matrix m n α) :=
pi.normed_space

end normed_space


section frobenius

instance frobenius_semi_normed_group [semi_normed_group α] :
  semi_normed_group (matrix m n α) :=
(by apply_instance : semi_normed_group (pi_Lp 2 (λ i : m, pi_Lp 2 (λ j : n, α))))

instance frobenius_normed_group [normed_group α] :
  normed_group (matrix m n α) :=
(by apply_instance : normed_group (pi_Lp 2 (λ i : m, pi_Lp 2 (λ j : n, α))))

instance frobenius_normed_space [normed_field R] [semi_normed_group α] [normed_space R α] :
  normed_space R (matrix m n α) :=
(by apply_instance : normed_space R (pi_Lp 2 (λ i : m, pi_Lp 2 (λ j : n, α))))

open_locale matrix big_operators

lemma frobenius_nnorm_mul [is_R_or_C α] (A : matrix l m α) (B : matrix m n α) :
  ∥A ⬝ B∥₊ ≤ ∥A∥₊ * ∥B∥₊ :=
begin
  simp_rw pi_Lp.nnorm_eq,
  rw [←nnreal.mul_rpow],
  simp_rw [←nnreal.rpow_mul, div_mul_cancel (1 : ℝ) two_ne_zero, nnreal.rpow_one,
    matrix.mul_apply],
  rw @finset.sum_comm _ n m,
  rw [finset.sum_mul_sum, finset.sum_product],
  refine nnreal.rpow_le_rpow _ one_half_pos.le,
  refine finset.sum_le_sum (λ i hi, finset.sum_le_sum $ λ j hj, _),
  rw [← nnreal.rpow_le_rpow_iff one_half_pos, ← nnreal.rpow_mul,
    mul_div_cancel' (1 : ℝ) two_ne_zero, nnreal.rpow_one, nnreal.mul_rpow,
      ←pi_Lp.nnorm_eq, ←pi_Lp.nnorm_eq],
  dsimp,
  let a : pi_Lp 2 _ := A i,
  let a' : pi_Lp 2 _ := λ j, star (a j),
  let b : pi_Lp 2 _ := λ k, B k j,
  letI : inner_product_space α (pi_Lp 2 (λ i : m, α)) := pi_Lp.inner_product_space _,
  change ∥∑ k, a k * b k∥₊ ≤ ∥a∥₊ * ∥b∥₊,
  convert nnorm_inner_le_nnorm a' b using 2,
  { simp,
    simp_rw [star_ring_end_apply, star_star], },
  simp [pi_Lp.nnorm_eq, a'],
  simp_rw [star_ring_end_apply, nnorm_star],
end


lemma frobenius_norm_mul [is_R_or_C α] (A : matrix l m α) (B : matrix m n α) :
  ∥A ⬝ B∥ ≤ ∥A∥ * ∥B∥ :=
frobenius_nnorm_mul A B

instance frobenius_normed_ring [is_R_or_C α] : normed_ring (matrix m m α) :=
{ norm := has_norm.norm,
  norm_mul := frobenius_norm_mul,
  ..(matrix.frobenius_normed_group : normed_group (matrix m m α)) }

end frobenius
end matrix
