/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import linear_algebra.dual
import linear_algebra.matrix.to_lin
/-!
# Dual space, linear maps and matrices.

This file contains some results on the matrix corresponding to the
transpose of a linear map (in the dual space).

## Tags

matrix, linear_map, transpose, dual
-/


open_locale matrix

section transpose

variables {K V₁ V₂ ι₁ ι₂ : Type*} [field K]
          [add_comm_group V₁] [module K V₁]
          [add_comm_group V₂] [module K V₂]
          [fintype ι₁] [fintype ι₂] [decidable_eq ι₁] [decidable_eq ι₂]
          {B₁ : basis ι₁ K V₁}
          {B₂ : basis ι₂ K V₂}

@[simp] lemma linear_map.to_matrix_transpose (u : V₁ →ₗ[K] V₂) :
  linear_map.to_matrix B₂.dual_basis B₁.dual_basis (module.dual.transpose u) =
    (linear_map.to_matrix B₁ B₂ u)ᵀ :=
begin
  ext i j,
  simp only [linear_map.to_matrix_apply, module.dual.transpose_apply, B₁.dual_basis_repr,
             B₂.dual_basis_apply, matrix.transpose_apply, linear_map.comp_apply]
end

@[simp] lemma matrix.to_lin_transpose (M : matrix ι₁ ι₂ K) :
  matrix.to_lin B₁.dual_basis B₂.dual_basis Mᵀ =
    module.dual.transpose (matrix.to_lin B₂ B₁ M) :=
begin
  apply (linear_map.to_matrix B₁.dual_basis B₂.dual_basis).injective,
  rw [linear_map.to_matrix_to_lin, linear_map.to_matrix_transpose, linear_map.to_matrix_to_lin]
end

end transpose
