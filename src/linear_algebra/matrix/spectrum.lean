/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import analysis.inner_product_space.spectrum
import linear_algebra.matrix.hermitian

/-! # Spectral theory of hermitian matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves the spectral theorem for matrices. The proof of the spectral theorem is based on
the spectral theorem for linear maps (`diagonalization_basis_apply_self_apply`).

## Tags

spectral theorem, diagonalization theorem

-/

namespace matrix

variables {𝕜 : Type*} [is_R_or_C 𝕜] [decidable_eq 𝕜] {n : Type*} [fintype n] [decidable_eq n]
variables {A : matrix n n 𝕜}

open_locale matrix
open_locale big_operators

namespace is_hermitian

variables (hA : A.is_hermitian)

/-- The eigenvalues of a hermitian matrix, indexed by `fin (fintype.card n)` where `n` is the index
type of the matrix. -/
noncomputable def eigenvalues₀ : fin (fintype.card n) → ℝ :=
(is_hermitian_iff_is_symmetric.1 hA).eigenvalues finrank_euclidean_space

/-- The eigenvalues of a hermitian matrix, reusing the index `n` of the matrix entries. -/
noncomputable def eigenvalues : n → ℝ :=
λ i, hA.eigenvalues₀ $ (fintype.equiv_of_card_eq (fintype.card_fin _)).symm i

/-- A choice of an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def eigenvector_basis : orthonormal_basis n 𝕜 (euclidean_space 𝕜 n) :=
((is_hermitian_iff_is_symmetric.1 hA).eigenvector_basis finrank_euclidean_space).reindex
  (fintype.equiv_of_card_eq (fintype.card_fin _))

/-- A matrix whose columns are an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def eigenvector_matrix : matrix n n 𝕜 :=
(pi_Lp.basis_fun _ 𝕜 n).to_matrix (eigenvector_basis hA).to_basis

/-- The inverse of `eigenvector_matrix` -/
noncomputable def eigenvector_matrix_inv : matrix n n 𝕜 :=
(eigenvector_basis hA).to_basis.to_matrix (pi_Lp.basis_fun _ 𝕜 n)

lemma eigenvector_matrix_mul_inv :
  hA.eigenvector_matrix ⬝ hA.eigenvector_matrix_inv = 1 :=
by apply basis.to_matrix_mul_to_matrix_flip

noncomputable instance : invertible hA.eigenvector_matrix_inv :=
invertible_of_left_inverse _ _ hA.eigenvector_matrix_mul_inv

noncomputable instance : invertible hA.eigenvector_matrix :=
invertible_of_right_inverse _ _ hA.eigenvector_matrix_mul_inv

lemma eigenvector_matrix_apply (i j : n) : hA.eigenvector_matrix i j = hA.eigenvector_basis j i :=
by simp_rw [eigenvector_matrix, basis.to_matrix_apply, orthonormal_basis.coe_to_basis,
    pi_Lp.basis_fun_repr]

lemma eigenvector_matrix_inv_apply (i j : n) :
  hA.eigenvector_matrix_inv i j = star (hA.eigenvector_basis i j) :=
begin
  rw [eigenvector_matrix_inv, basis.to_matrix_apply, orthonormal_basis.coe_to_basis_repr_apply,
    orthonormal_basis.repr_apply_apply, pi_Lp.basis_fun_apply, pi_Lp.equiv_symm_single,
    euclidean_space.inner_single_right, one_mul, is_R_or_C.star_def],
end

lemma conj_transpose_eigenvector_matrix_inv : hA.eigenvector_matrix_invᴴ = hA.eigenvector_matrix :=
by { ext i j,
  rw [conj_transpose_apply, eigenvector_matrix_inv_apply, eigenvector_matrix_apply, star_star] }

lemma conj_transpose_eigenvector_matrix : hA.eigenvector_matrixᴴ = hA.eigenvector_matrix_inv :=
by rw [← conj_transpose_eigenvector_matrix_inv, conj_transpose_conj_transpose]

/-- *Diagonalization theorem*, *spectral theorem* for matrices; A hermitian matrix can be
diagonalized by a change of basis.

For the spectral theorem on linear maps, see `diagonalization_basis_apply_self_apply`. -/
theorem spectral_theorem :
  hA.eigenvector_matrix_inv ⬝ A =
    diagonal (coe ∘ hA.eigenvalues) ⬝ hA.eigenvector_matrix_inv :=
begin
  rw [eigenvector_matrix_inv, pi_Lp.basis_to_matrix_basis_fun_mul],
  ext i j,
  have := is_hermitian_iff_is_symmetric.1 hA,
  convert this.diagonalization_basis_apply_self_apply finrank_euclidean_space
    (euclidean_space.single j 1)
    ((fintype.equiv_of_card_eq (fintype.card_fin _)).symm i) using 1,
  { dsimp only [euclidean_space.single, to_euclidean_lin_pi_Lp_equiv_symm, to_lin'_apply,
      matrix.of_apply, is_hermitian.eigenvector_basis],
    simp_rw [mul_vec_single, mul_one, orthonormal_basis.coe_to_basis_repr_apply,
      orthonormal_basis.repr_reindex],
    refl },
  { simp only [diagonal_mul, (∘), eigenvalues],
    rw [eigenvector_basis, basis.to_matrix_apply,
      orthonormal_basis.coe_to_basis_repr_apply, orthonormal_basis.repr_reindex,
      eigenvalues₀, pi_Lp.basis_fun_apply, pi_Lp.equiv_symm_single] }
end

lemma eigenvalues_eq (i : n) :
  hA.eigenvalues i =
    is_R_or_C.re ((star (hA.eigenvector_matrixᵀ i) ⬝ᵥ (A.mul_vec (hA.eigenvector_matrixᵀ i)))) :=
begin
  have := hA.spectral_theorem,
  rw [←matrix.mul_inv_eq_iff_eq_mul_of_invertible] at this,
  have := congr_arg is_R_or_C.re (congr_fun (congr_fun this i) i),
  rw [diagonal_apply_eq, is_R_or_C.of_real_re, inv_eq_left_inv hA.eigenvector_matrix_mul_inv,
    ← conj_transpose_eigenvector_matrix, mul_mul_apply] at this,
  exact this.symm,
end

/-- The determinant of a hermitian matrix is the product of its eigenvalues. -/
lemma det_eq_prod_eigenvalues : det A = ∏ i, hA.eigenvalues i :=
begin
  apply mul_left_cancel₀ (det_ne_zero_of_left_inverse (eigenvector_matrix_mul_inv hA)),
  rw [←det_mul, spectral_theorem, det_mul, mul_comm, det_diagonal]
end

end is_hermitian

end matrix
