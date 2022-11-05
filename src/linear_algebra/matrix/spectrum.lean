/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import analysis.inner_product_space.spectrum
import linear_algebra.matrix.hermitian

/-! # Spectral theory of hermitian matrices

This file proves the spectral theorem for matrices. The proof of the spectral theorem is based on
the spectral theorem for linear maps (`diagonalization_basis_apply_self_apply`).

## Tags

spectral theorem, diagonalization theorem

-/

namespace matrix

open_locale matrix


variables {𝕜 : Type*} [is_R_or_C 𝕜] [decidable_eq 𝕜] {n : Type*} [fintype n] [decidable_eq n]
variables {A : matrix n n 𝕜}

open_locale matrix
open_locale big_operators

lemma _root_.euclidean_space.basis_to_matrix_single_mul
  (b : basis n 𝕜 (euclidean_space 𝕜 n)) (A : matrix n n 𝕜) :
  b.to_matrix (λ i, euclidean_space.single i 1) ⬝ A =
    of (λ i j, b.repr ((pi_Lp.equiv _ _).symm (Aᵀ j)) i) :=
begin
  have := basis_to_matrix_basis_fun_mul (b.map (pi_Lp.linear_equiv _ 𝕜 _)) A,
  simp_rw [basis.to_matrix_map, basis.map_repr, function.comp, pi.basis_fun_apply,
    linear_map.std_basis, linear_map.coe_single, linear_equiv.trans_apply,
    pi_Lp.linear_equiv_symm_apply, pi_Lp.equiv_symm_single] at this,
  rw this,
end

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
((pi.basis_fun 𝕜 n).map
  (pi_Lp.linear_equiv _ 𝕜 (λ _ : n, 𝕜)).symm).to_matrix (eigenvector_basis hA).to_basis

/-- The inverse of `eigenvector_matrix` -/
noncomputable def eigenvector_matrix_inv : matrix n n 𝕜 :=
(eigenvector_basis hA).to_basis.to_matrix (λ i, euclidean_space.single i 1)

lemma eigenvector_matrix_mul_inv :
  hA.eigenvector_matrix ⬝ hA.eigenvector_matrix_inv = 1 :=
by apply basis.to_matrix_mul_to_matrix_flip

#check basis.to_matrix_mul_to_matrix_flip

noncomputable instance : invertible hA.eigenvector_matrix_inv :=
invertible_of_left_inverse _ _ hA.eigenvector_matrix_mul_inv

noncomputable instance : invertible hA.eigenvector_matrix :=
invertible_of_right_inverse _ _ hA.eigenvector_matrix_mul_inv

lemma eigenvector_matrix_apply (i j : n) : hA.eigenvector_matrix i j = hA.eigenvector_basis j i :=
by simp_rw [eigenvector_matrix, basis.to_matrix_apply, orthonormal_basis.coe_to_basis,
    basis.map_repr, linear_equiv.symm_symm, linear_equiv.trans_apply, pi_Lp.linear_equiv_apply,
    pi.basis_fun_repr, pi_Lp.equiv_apply]

lemma eigenvector_matrix_inv_apply (i j : n) :
  hA.eigenvector_matrix_inv i j = star (hA.eigenvector_basis i j) :=
begin
  rw [eigenvector_matrix_inv, basis.to_matrix_apply, orthonormal_basis.coe_to_basis_repr_apply,
    orthonormal_basis.repr_apply_apply, euclidean_space.inner_single_right],
  simp only [one_mul, conj_transpose_apply, is_R_or_C.star_def],
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
  simp_rw [eigenvector_matrix_inv, pi.basis_fun_apply],
  dsimp [linear_map.std_basis, linear_map.coe_single, pi_Lp.equiv_symm_single],
  rw euclidean_space.basis_to_matrix_single_mul,
   -- equiv.apply_symm_apply, basis_to_matrix_basis_fun_mul],
  ext i j,
  have : linear_map.is_symmetric _ := is_hermitian_iff_is_symmetric.1 hA,
  convert this.diagonalization_basis_apply_self_apply finrank_euclidean_space
    (euclidean_space.single j 1)
    ((fintype.equiv_of_card_eq (fintype.card_fin _)).symm i),
  { dsimp only [linear_equiv.conj_apply_apply, pi_Lp.linear_equiv_apply,
      pi_Lp.linear_equiv_symm_apply, pi_Lp.equiv_single, linear_map.std_basis,
      linear_map.coe_single, pi_Lp.equiv_symm_single, linear_equiv.symm_symm,
      eigenvector_basis, to_lin'_apply],
    simp only [basis.to_matrix, basis.coe_to_orthonormal_basis_repr, basis.equiv_fun_apply],
    simp_rw [orthonormal_basis.coe_to_basis_repr_apply, orthonormal_basis.reindex_repr,
      linear_equiv.symm_symm, pi_Lp.linear_equiv_apply, pi_Lp.equiv_single, mul_vec_single,
      mul_one],
    refl },
  { simp only [diagonal_mul, (∘), eigenvalues, eigenvector_basis],
    rw [basis.to_matrix_apply,
      orthonormal_basis.coe_to_basis_repr_apply, orthonormal_basis.reindex_repr,
      eigenvalues₀] }
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
