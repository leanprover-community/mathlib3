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

lemma is_symm.ext_iff {A : matrix n n α} : A.is_symm ↔ ∀ i j, Aᵀ i j = A i j :=
by rw [is_symm, matrix.ext_iff]

lemma is_symm.ext_iff' {A : matrix n n α} : A.is_symm ↔ ∀ i j, A j i = A i j :=
is_symm.ext_iff

lemma is_symm.apply {A : matrix n n α} (h : A.is_symm) (i j : n) : Aᵀ i j = A i j :=
is_symm.ext_iff.1 h i j

lemma is_symm.apply' {A : matrix n n α} (h : A.is_symm) (i j : n) : A j i = A i j :=
is_symm.apply h i j

lemma is_symm.ext {A : matrix n n α} : (∀ i j, Aᵀ i j = A i j) → A.is_symm :=
is_symm.ext_iff.2

lemma is_symm.ext' {A : matrix n n α} : (∀ i j, A j i = A i j) → A.is_symm :=
is_symm.ext

/-- `A ⬝ Aᵀ` is symmertric. -/
lemma is_symm_mul_transpose_self [fintype n] [comm_semiring α] (A : matrix n n α) :
  (A ⬝ Aᵀ).is_symm :=
transpose_mul _ _

/-- `Aᵀ ⬝ A` is symmertric. -/
lemma is_symm_transpose_mul_self [fintype n] [comm_semiring α] (A : matrix n n α) :
  (A ⬝ Aᵀ).is_symm :=
by simp [matrix.is_symm, transpose_mul]

/-- `A + Aᵀ` is symmertric. -/
lemma is_symm_add_transpose_self [fintype n] [add_comm_semigroup α] (A : matrix n n α) :
  (A + Aᵀ).is_symm :=
by simp [matrix.is_symm, add_comm]

/-- `Aᵀ + A` is symmertric. -/
lemma is_symm_transpose_add_self [fintype n] [add_comm_semigroup α] (A : matrix n n α) :
  (Aᵀ + A).is_symm :=
by simp [matrix.is_symm, add_comm]

/-- The identity matrix is symmetric. -/
@[simp] lemma is_symm_one [decidable_eq n] [has_zero α] [has_one α] :
  (1 : matrix n n α).is_symm :=
by {ext, simp}

lemma is_symm.transpose {A : matrix n n α} (h : A.is_symm) :
  Aᵀ.is_symm :=
by ext; simp [h.apply']

lemma is_symm.conj_transpose [has_star α] {A : matrix n n α} (h : A.is_symm) :
  Aᴴ.is_symm :=
by ext; simp [h.apply']

lemma is_symm.map {A : matrix n n α} (h : A.is_symm) (f : α → β) :
  (A.map f).is_symm :=
by ext; simp [h.apply']

@[simp] lemma is_symm.neg
[has_neg α] {A : matrix n n α} (h : A.is_symm) :
(-A).is_symm :=
by ext; simp [h.apply']

@[simp] lemma is_symm.smul
[has_scalar R α] {A : matrix n n α} (h : A.is_symm) (k : R) :
(k • A).is_symm :=
by ext; simp [h.apply']

/-- The diagonal matrix `diagonal v` is symmetric. -/
@[simp] lemma is_symm_diagonal [decidable_eq n] [has_zero α] (v : n → α) :
(diagonal v).is_symm :=
begin
  ext,
  by_cases i = j; simp [*, diagonal],
  intro g, exfalso, exact h g.symm
end

/-- A block matrix `A.from_blocks B C D` is symmetric,
    if `A` and `D` are symmetric and `Bᵀ = C`. -/
lemma is_symm_from_blocks
  {A : matrix m m α} {B : matrix m n α} {C : matrix n m α} {D : matrix n n α}
  (h1 : A.is_symm) (h2 : D.is_symm) (h3 : Bᵀ = C) :
  (A.from_blocks B C D).is_symm :=
begin
  have h4 : Cᵀ = B, {rw ← h3, simp},
  unfold matrix.is_symm,
  rw from_blocks_transpose,
  congr;
  assumption
end

/-- If a block matrix `A.from_blocks B C D` is symmetric,
    `A`, `D` are symmetric, and `Cᵀ = B`, and `Bᵀ = C`.
    This is the converse of `matrix.is_symm_from_blocks`. -/
lemma block_conditions_of_is_symm
{A : matrix m m α} {B : matrix m n α} {C : matrix n m α} {D : matrix n n α}
(h : (A.from_blocks B C D).is_symm) :
(A.is_symm) ∧ (D.is_symm) ∧ (Cᵀ = B) ∧ (Bᵀ = C) :=
begin
  unfold matrix.is_symm at h,
  rw from_blocks_transpose at h,
  have h1 : (Aᵀ.from_blocks Cᵀ Bᵀ Dᵀ).to_blocks₁₁ = (A.from_blocks B C D).to_blocks₁₁, {rw h},
  have h2 : (Aᵀ.from_blocks Cᵀ Bᵀ Dᵀ).to_blocks₁₂ = (A.from_blocks B C D).to_blocks₁₂, {rw h},
  have h3 : (Aᵀ.from_blocks Cᵀ Bᵀ Dᵀ).to_blocks₂₁ = (A.from_blocks B C D).to_blocks₂₁, {rw h},
  have h4 : (Aᵀ.from_blocks Cᵀ Bᵀ Dᵀ).to_blocks₂₂ = (A.from_blocks B C D).to_blocks₂₂, {rw h},
  simp at *,
  use ⟨h1, h4, h2, h3⟩
end

end matrix
