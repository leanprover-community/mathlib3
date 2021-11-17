/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import data.matrix.basic

/-!
# Orthogonal

This file contains definitions and properties concerning orthogonality of rows and columns.

## Main results

- `matrix.has_orthogonal_rows`:
  `A.has_orthogonal_rows` means `A` has orthogonal (with respect to `dot_product`) rows.
- `matrix.has_orthogonal_cols`:
  `A.has_orthogonal_cols` means `A` has orthogonal (with respect to `dot_product`) columns.

## Tags

orthogonal
-/

namespace matrix

variables {α n m : Type*}
variables [has_mul α] [add_comm_monoid α]
variables (A : matrix m n α)

open_locale matrix

/-- `A.has_orthogonal_rows` means matrix `A` has orthogonal rows (with respect to
`matrix.dot_product`). -/
def has_orthogonal_rows [fintype n] : Prop :=
∀ ⦃i₁ i₂⦄, i₁ ≠ i₂ → dot_product (A i₁) (A i₂) = 0

/-- `A.has_orthogonal_rows` means matrix `A` has orthogonal columns (with respect to
`matrix.dot_product`). -/
def has_orthogonal_cols [fintype m] : Prop :=
has_orthogonal_rows Aᵀ

/-- `Aᵀ` has orthogonal rows iff `A` has orthogonal columns. -/
@[simp] lemma transpose_has_orthogonal_rows_iff_has_orthogonal_cols [fintype m] :
  Aᵀ.has_orthogonal_rows ↔ A.has_orthogonal_cols :=
iff.rfl

/-- `Aᵀ` has orthogonal columns iff `A` has orthogonal rows. -/
@[simp] lemma transpose_has_orthogonal_cols_iff_has_orthogonal_rows [fintype n] :
  Aᵀ.has_orthogonal_cols ↔ A.has_orthogonal_rows :=
iff.rfl

variables {A}

lemma has_orthogonal_rows.has_orthogonal_cols
  [fintype m] (h : Aᵀ.has_orthogonal_rows) :
  A.has_orthogonal_cols := h

lemma has_orthogonal_cols.transpose_has_orthogonal_rows
  [fintype m] (h : A.has_orthogonal_cols) :
  Aᵀ.has_orthogonal_rows := h

lemma has_orthogonal_cols.has_orthogonal_rows
  [fintype n] (h : Aᵀ.has_orthogonal_cols) :
  A.has_orthogonal_rows := h

lemma has_orthogonal_rows.transpose_has_orthogonal_cols
  [fintype n] (h : A.has_orthogonal_rows) :
  Aᵀ.has_orthogonal_cols := h

end matrix
