/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import analysis.inner_product_space.gram_schmidt_ortho
import linear_algebra.matrix.pos_def

/-! # LDL decomposition

This file proves the LDL-decomposition of matricies: Any positive definite matrix `S` can be
decomposed as `S = LDLᴴ` where `L` is a lower-triangular matrix and `D` is a diagonal matrix.

## Main definitions

 * `LDL.lower` is the lower triangular matrix `L`.
 * `LDL.lower_inv` is the inverse of the lower triangular matrix `L`.
 * `LDL.diag` is the diagonal matrix `D`.

## Main result

* `ldl_decomposition` states that any positive definite matrix can be decomposed as `LDLᴴ`.

## TODO

* Prove that `LDL.lower` is lower triangular from `LDL.lower_inv_triangular`.

-/

variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {n : Type*} [linear_order n] [is_well_order n (<)] [locally_finite_order_bot n]

local notation `⟪`x`, `y`⟫` :=
@inner 𝕜 (n → 𝕜) (pi_Lp.inner_product_space (λ _, 𝕜)).to_has_inner x y

open matrix
open_locale matrix
variables {S : matrix n n 𝕜} [fintype n] (hS : S.pos_def)

/-- The inverse of the lower triangular matrix `L` of the LDL-decomposition. It is obtained by
applying Gram-Schmidt-Orthogonalization w.r.t. the inner product induced by `Sᵀ` on the standard
basis vectors `pi.basis_fun`. -/
noncomputable def LDL.lower_inv : matrix n n 𝕜 :=
@gram_schmidt
  𝕜 (n → 𝕜) _ (inner_product_space.of_matrix hS.transpose) n _ _ _ (λ k, pi.basis_fun 𝕜 n k)

lemma LDL.lower_inv_eq_gram_schmidt_basis :
  LDL.lower_inv hS = ((pi.basis_fun 𝕜 n).to_matrix
    (@gram_schmidt_basis 𝕜 (n → 𝕜) _
    (inner_product_space.of_matrix hS.transpose) n _ _ _ (pi.basis_fun 𝕜 n)))ᵀ :=
begin
  ext i j,
  rw [LDL.lower_inv, basis.coe_pi_basis_fun.to_matrix_eq_transpose, coe_gram_schmidt_basis],
  refl
end

noncomputable instance LDL.invertible_lower_inv : invertible (LDL.lower_inv hS) :=
begin
  rw [LDL.lower_inv_eq_gram_schmidt_basis],
  haveI := basis.invertible_to_matrix (pi.basis_fun 𝕜 n)
    (@gram_schmidt_basis 𝕜 (n → 𝕜) _ (inner_product_space.of_matrix hS.transpose)
      n _ _ _ (pi.basis_fun 𝕜 n)),
  apply_instance
end

lemma LDL.lower_inv_orthogonal {i j : n} (h₀ : i ≠ j) :
  ⟪(LDL.lower_inv hS i), Sᵀ.mul_vec (LDL.lower_inv hS j)⟫ = 0 :=
show @inner 𝕜 (n → 𝕜) (inner_product_space.of_matrix hS.transpose).to_has_inner
    (LDL.lower_inv hS i)
    (LDL.lower_inv hS j) = 0,
by apply gram_schmidt_orthogonal _ _ h₀

/-- The entries of the diagonal matrix `D` of the LDL decomposition. -/
noncomputable def LDL.diag_entries : n → 𝕜 :=
  λ i, ⟪star (LDL.lower_inv hS i), S.mul_vec (star (LDL.lower_inv hS i))⟫

/-- The diagonal matrix `D` of the LDL decomposition. -/
noncomputable def LDL.diag : matrix n n 𝕜 := matrix.diagonal (LDL.diag_entries hS)

lemma LDL.lower_inv_triangular {i j : n} (hij : i < j) :
  LDL.lower_inv hS i j = 0 :=
by rw [← @gram_schmidt_triangular 𝕜 (n → 𝕜) _ (inner_product_space.of_matrix hS.transpose) n _ _ _
    i j hij (pi.basis_fun 𝕜 n), pi.basis_fun_repr, LDL.lower_inv]

/-- Inverse statement of **LDL decomposition**: we can conjugate a positive definite matrix
by some lower triangular matrix and get a diagonal matrix. -/
lemma LDL.diag_eq_lower_inv_conj : LDL.diag hS = LDL.lower_inv hS ⬝ S ⬝ (LDL.lower_inv hS)ᴴ :=
begin
  ext i j,
  by_cases hij : i = j,
  { simpa only [hij, LDL.diag, diagonal_apply_eq, LDL.diag_entries, matrix.mul_assoc, inner,
      pi.star_apply, is_R_or_C.star_def, star_ring_end_self_apply] },
  { simp only [LDL.diag, hij, diagonal_apply_ne, ne.def, not_false_iff, mul_mul_apply],
    rw [conj_transpose, transpose_map, transpose_transpose, dot_product_mul_vec,
      (LDL.lower_inv_orthogonal hS (λ h : j = i, hij h.symm)).symm,
      ← inner_conj_sym, mul_vec_transpose, euclidean_space.inner_eq_star_dot_product,
      ← is_R_or_C.star_def, ← star_dot_product_star, dot_product_comm, star_star],
    refl }
end

/-- The lower triangular matrix `L` of the LDL decomposition. -/
noncomputable def LDL.lower := (LDL.lower_inv hS)⁻¹

/-- **LDL decomposition**: any positive definite matrix `S` can be
decomposed as `S = LDLᴴ` where `L` is a lower-triangular matrix and `D` is a diagonal matrix.  -/
theorem LDL.lower_conj_diag :
  LDL.lower hS ⬝ LDL.diag hS ⬝ (LDL.lower hS)ᴴ = S :=
begin
  rw [LDL.lower, conj_transpose_nonsing_inv, matrix.mul_assoc,
    matrix.inv_mul_eq_iff_eq_mul_of_invertible (LDL.lower_inv hS),
    matrix.mul_inv_eq_iff_eq_mul_of_invertible],
  exact LDL.diag_eq_lower_inv_conj hS,
end
