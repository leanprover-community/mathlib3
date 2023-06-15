/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import linear_algebra.charpoly.basic
import linear_algebra.matrix.basis

/-!

# Characteristic polynomial

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main result

* `linear_map.charpoly_to_matrix f` : `charpoly f` is the characteristic polynomial of the matrix
of `f` in any basis.

-/

universes u v w

variables {R : Type u} {M : Type v} [comm_ring R] [nontrivial R]
variables [add_comm_group M] [module R M] [module.free R M] [module.finite R M] (f : M →ₗ[R] M)

open_locale classical matrix

noncomputable theory

open module.free polynomial matrix

namespace linear_map

section basic

/-- `charpoly f` is the characteristic polynomial of the matrix of `f` in any basis. -/
@[simp] lemma charpoly_to_matrix {ι : Type w} [fintype ι] (b : basis ι R M) :
  (to_matrix b b f).charpoly = f.charpoly :=
begin
  set A := to_matrix b b f,
  set b' := choose_basis R M,
  set ι' := choose_basis_index R M,
  set A' := to_matrix b' b' f,
  set e := basis.index_equiv b b',
  set φ := reindex_linear_equiv R R e e,
  set φ₁ := reindex_linear_equiv R R e (equiv.refl ι'),
  set φ₂ := reindex_linear_equiv R R (equiv.refl ι') (equiv.refl ι'),
  set φ₃ := reindex_linear_equiv R R (equiv.refl ι') e,
  set P := b.to_matrix b',
  set Q := b'.to_matrix b,

  have hPQ : C.map_matrix (φ₁ P) ⬝ (C.map_matrix (φ₃ Q)) = 1,
  { rw [ring_hom.map_matrix_apply, ring_hom.map_matrix_apply, ← matrix.map_mul,
      @reindex_linear_equiv_mul _ ι' _ _ _ _ R R, basis.to_matrix_mul_to_matrix_flip,
      reindex_linear_equiv_one, ← ring_hom.map_matrix_apply, ring_hom.map_one] },

  calc A.charpoly = (reindex e e A).charpoly : (charpoly_reindex _ _).symm
  ... = (scalar ι' X - C.map_matrix (φ A)).det : rfl
  ... = (scalar ι' X - C.map_matrix (φ (P ⬝ A' ⬝ Q))).det :
    by rw [basis_to_matrix_mul_linear_map_to_matrix_mul_basis_to_matrix]
  ... = (scalar ι' X - C.map_matrix (φ₁ P ⬝ φ₂ A' ⬝ φ₃ Q)).det :
    by rw [reindex_linear_equiv_mul, reindex_linear_equiv_mul]
  ... = (scalar ι' X - (C.map_matrix (φ₁ P) ⬝ C.map_matrix A' ⬝ C.map_matrix (φ₃ Q))).det : by simp
  ... = (scalar ι' X ⬝ C.map_matrix (φ₁ P) ⬝ (C.map_matrix (φ₃ Q)) -
    (C.map_matrix (φ₁ P) ⬝ C.map_matrix A' ⬝ C.map_matrix (φ₃ Q))).det :
      by { rw [matrix.mul_assoc ((scalar ι') X), hPQ, matrix.mul_one] }
  ... = (C.map_matrix (φ₁ P) ⬝ scalar ι' X ⬝ (C.map_matrix (φ₃ Q)) -
    (C.map_matrix (φ₁ P) ⬝ C.map_matrix A' ⬝ C.map_matrix (φ₃ Q))).det : by simp
  ... = (C.map_matrix (φ₁ P) ⬝ (scalar ι' X - C.map_matrix A') ⬝ C.map_matrix (φ₃ Q)).det :
    by rw [← matrix.sub_mul, ← matrix.mul_sub]
  ... = (C.map_matrix (φ₁ P)).det * (scalar ι' X - C.map_matrix A').det *
    (C.map_matrix (φ₃ Q)).det : by rw [det_mul, det_mul]
  ... = (C.map_matrix (φ₁ P)).det * (C.map_matrix (φ₃ Q)).det *
    (scalar ι' X - C.map_matrix A').det : by ring
  ... = (scalar ι' X - C.map_matrix A').det : by rw [← det_mul, hPQ, det_one, one_mul]
  ... = f.charpoly : rfl
end

end basic

end linear_map
