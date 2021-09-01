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

 * `matrix.is_sym `: a matrix `A : matrix n n α` is "symmetric" if `Aᵀ = A`.

## Tags

sym, symmetric, matrix
-/

variables {α n m R : Type*} [fintype n] [fintype m]

namespace matrix

open_locale matrix

/-- A matrix `A : matrix n n α` is "symmetric" if `Aᵀ = A`. -/
def is_sym (A : matrix n n α) : Prop := Aᵀ = A

lemma is_sym.eq {A : matrix n n α} (h : A.is_sym) : Aᵀ = A := h

lemma is_sym.ext_iff {A : matrix n n α} : A.is_sym ↔ ∀ i j, Aᵀ i j = A i j :=
by rw [is_sym, matrix.ext_iff]

lemma is_sym.ext_iff' {A : matrix n n α} : A.is_sym ↔ ∀ i j, A j i = A i j :=
is_sym.ext_iff

lemma is_sym.apply {A : matrix n n α} (h : A.is_sym) (i j : n) : Aᵀ i j = A i j :=
is_sym.ext_iff.1 h i j

lemma is_sym.apply' {A : matrix n n α} (h : A.is_sym) (i j : n) : A j i = A i j :=
is_sym.apply h i j

lemma is_sym.ext {A : matrix n n α} : (∀ i j, Aᵀ i j = A i j) → A.is_sym :=
is_sym.ext_iff.2

lemma is_sym.ext' {A : matrix n n α} : (∀ i j, A j i = A i j) → A.is_sym :=
is_sym.ext

/-- A block matrix `A.from_blocks B C D` is symmetric,
    if `A` and `D` are symmetric and `Bᵀ = C`. -/
lemma is_sym_from_blocks
  {A : matrix m m α} {B : matrix m n α} {C : matrix n m α} {D : matrix n n α}
  (h1 : A.is_sym) (h2 : D.is_sym) (h3 : Bᵀ = C) :
  (A.from_blocks B C D).is_sym :=
begin
  have h4 : Cᵀ = B, {rw ← h3, simp},
  unfold matrix.is_sym,
  rw from_blocks_transpose,
  congr;
  assumption
end

/-- `A ⬝ Aᵀ` is symmertric. -/
lemma is_sym_mul_transpose_self [comm_semiring α] (A : matrix n n α) :
  (A ⬝ Aᵀ).is_sym :=
by simp [matrix.is_sym, transpose_mul]

/-- The identity matrix is symmetric. -/
@[simp] lemma is_sym_one [decidable_eq n] [has_zero α] [has_one α] :
  (1 : matrix n n α).is_sym := by {ext, simp}

/-- The negtive identity matrix is symmetric. -/
@[simp] lemma is_sym_neg_one [decidable_eq n] [has_zero α] [has_one α] [has_neg α] :
  (-1 : matrix n n α).is_sym := by {ext, simp}

@[simp] lemma is_sym.neg
[has_neg α] {A : matrix n n α} (h : A.is_sym) :
(-A).is_sym :=
by ext; simp [h.apply']

@[simp] lemma is_sym.smul
[has_scalar R α] {A : matrix n n α} (h : A.is_sym) (k : R) :
(k • A).is_sym :=
by ext; simp [h.apply']

/-- The identity matrix multiplied by any scalar `k` is symmetric. -/
@[simp] lemma is_sym_of_smul_one
[decidable_eq n] [has_zero α] [has_one α] [has_scalar R α] (k : R) :
(k • (1 : matrix n n α)).is_sym :=
is_sym_one.smul k

/-- The diagonal matrix `diagonal v` is symmetric. -/
@[simp] lemma is_sym_diagonal [decidable_eq n] [has_zero α] (v : n → α) :
(diagonal v).is_sym :=
begin
  ext,
  by_cases i = j; simp [*, diagonal],
  intro g, exfalso, exact h g.symm
end

/- If a block matrix `A.from_blocks B C D` is symmetric,
    `A`, `D` are symmetric, and `Cᵀ = B`, and `Bᵀ = C`.-/
/-
lemma block_conditions_of_is_sym
{A : matrix m m α} {B : matrix m n α} {C : matrix n m α} {D : matrix n n α}
(h : (A.from_blocks B C D).is_sym) :
(A.is_sym) ∧ (D.is_sym) ∧ (Cᵀ = B) ∧ (Bᵀ = C) :=
begin
  unfold matrix.is_sym at h,
  rw from_blocks_transpose at h,
  have h1 : (Aᵀ.from_blocks Cᵀ Bᵀ Dᵀ).to_blocks₁₁ = (A.from_blocks B C D).to_blocks₁₁, {rw h},
  have h2 : (Aᵀ.from_blocks Cᵀ Bᵀ Dᵀ).to_blocks₁₂ = (A.from_blocks B C D).to_blocks₁₂, {rw h},
  have h3 : (Aᵀ.from_blocks Cᵀ Bᵀ Dᵀ).to_blocks₂₁ = (A.from_blocks B C D).to_blocks₂₁, {rw h},
  have h4 : (Aᵀ.from_blocks Cᵀ Bᵀ Dᵀ).to_blocks₂₂ = (A.from_blocks B C D).to_blocks₂₂, {rw h},
  simp at *,
  use ⟨h1, h4, h2, h3⟩
end
-/

end matrix
