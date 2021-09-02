/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import data.matrix.block

/-!
# Symmetric matrices

This file contains the definition and basic results about symmetric matrices.

## Main definition

 * `matrix.is_symm `: a matrix `A : matrix n n α` is "symmetric" if `Aᵀ = A`.

## Tags

symm, symmetric, matrix
-/

variables {α β n m R : Type*}

namespace matrix

open_locale matrix

/-- A matrix `A : matrix n n α` is "symmetric" if `Aᵀ = A`. -/
def is_symm (A : matrix n n α) : Prop := Aᵀ = A

lemma is_symm.eq {A : matrix n n α} (h : A.is_symm) : Aᵀ = A := h

/-- A version of `matrix.ext_iff` that unfolds the `matrix.transpose`. -/
lemma is_symm.ext_iff {A : matrix n n α} : A.is_symm ↔ ∀ i j, A j i = A i j :=
matrix.ext_iff.symm

/-- A version of `matrix.ext` that unfolds the `matrix.transpose`. -/
@[ext]
lemma is_symm.ext {A : matrix n n α} : (∀ i j, A j i = A i j) → A.is_symm :=
matrix.ext

lemma is_symm.apply {A : matrix n n α} (h : A.is_symm) (i j : n) : A j i = A i j :=
is_symm.ext_iff.1 h i j

lemma is_symm_mul_transpose_self [fintype n] [comm_semiring α] (A : matrix n n α) :
  (A ⬝ Aᵀ).is_symm :=
transpose_mul _ _

lemma is_symm_transpose_mul_self [fintype n] [comm_semiring α] (A : matrix n n α) :
  (A ⬝ Aᵀ).is_symm :=
transpose_mul _ _

lemma is_symm_add_transpose_self [add_comm_semigroup α] (A : matrix n n α) :
  (A + Aᵀ).is_symm :=
add_comm _ _

lemma is_symm_transpose_add_self [add_comm_semigroup α] (A : matrix n n α) :
  (Aᵀ + A).is_symm :=
add_comm _ _

@[simp] lemma is_symm_zero [has_zero α] :
  (0 : matrix n n α).is_symm :=
transpose_zero

@[simp] lemma is_symm_one [decidable_eq n] [has_zero α] [has_one α] :
  (1 : matrix n n α).is_symm :=
transpose_one

@[simp] lemma is_symm.map {A : matrix n n α} (h : A.is_symm) (f : α → β) :
  (A.map f).is_symm :=
transpose_map.symm.trans (h.symm ▸ rfl)

@[simp] lemma is_symm.transpose {A : matrix n n α} (h : A.is_symm) :
  Aᵀ.is_symm :=
congr_arg _ h

@[simp] lemma is_symm.conj_transpose [has_star α] {A : matrix n n α} (h : A.is_symm) :
  Aᴴ.is_symm :=
h.transpose.map _

@[simp] lemma is_symm.neg [has_neg α] {A : matrix n n α} (h : A.is_symm) :
  (-A).is_symm :=
(transpose_neg _).trans (congr_arg _ h)

@[simp] lemma is_symm.add {A B : matrix n n α} [has_add α] (hA : A.is_symm) (hB : B.is_symm) :
  (A + B).is_symm :=
(transpose_add _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp] lemma is_symm.sub {A B : matrix n n α} [has_sub α] (hA : A.is_symm) (hB : B.is_symm) :
  (A - B).is_symm :=
(transpose_sub _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp] lemma is_symm.smul [has_scalar R α] {A : matrix n n α} (h : A.is_symm) (k : R) :
  (k • A).is_symm :=
(transpose_smul _ _).trans (congr_arg _ h)

@[simp] lemma is_symm.minor {A : matrix n n α} (h : A.is_symm) (f : m → n) :
  (A.minor f f).is_symm :=
(transpose_minor _ _ _).trans (h.symm ▸ rfl)

/-- The diagonal matrix `diagonal v` is symmetric. -/
@[simp] lemma is_symm_diagonal [decidable_eq n] [has_zero α] (v : n → α) :
  (diagonal v).is_symm :=
diagonal_transpose _

/-- A block matrix `A.from_blocks B C D` is symmetric,
    if `A` and `D` are symmetric and `Bᵀ = C`. -/
lemma is_symm.from_blocks
  {A : matrix m m α} {B : matrix m n α} {C : matrix n m α} {D : matrix n n α}
  (hA : A.is_symm) (hBC : Bᵀ = C) (hD : D.is_symm) :
  (A.from_blocks B C D).is_symm :=
begin
  have hCB : Cᵀ = B, {rw ← hBC, simp},
  unfold matrix.is_symm,
  rw from_blocks_transpose,
  congr;
  assumption
end

/-- This is the `iff` version of `matrix.is_symm.from_blocks`. -/
lemma is_symm_from_blocks_iff
  {A : matrix m m α} {B : matrix m n α} {C : matrix n m α} {D : matrix n n α} :
  (A.from_blocks B C D).is_symm ↔ A.is_symm ∧ Bᵀ = C ∧ Cᵀ = B ∧ D.is_symm :=
⟨λ h, ⟨congr_arg to_blocks₁₁ h, congr_arg to_blocks₂₁ h,
       congr_arg to_blocks₁₂ h, congr_arg to_blocks₂₂ h⟩,
 λ ⟨hA, hBC, hCB, hD⟩, is_symm.from_blocks hA hBC hD⟩

end matrix
