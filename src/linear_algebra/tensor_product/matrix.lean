/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import data.matrix.kronecker
import linear_algebra.matrix.to_lin
import linear_algebra.tensor_product_basis

/-!
# Connections between `tensor_product` and `matrix`

This file contains results about the matrices corresponding to maps between tensor product types,
where the correspondance is induced by `basis.tensor_product`

Notably, `tensor_product.to_matrix_map` shows that taking  the tensor product of linear maps is
equivalent to taking the kronecker product of their matrix representations.
-/

variables {R : Type*} {M N P M' N' : Type*} {ι κ τ ι' κ' : Type*}
variables [decidable_eq ι] [decidable_eq κ] [decidable_eq τ]
variables [fintype ι] [fintype κ] [fintype τ] [fintype ι'] [fintype κ']
variables [comm_ring R]
variables [add_comm_group M] [add_comm_group N] [add_comm_group P]
variables [add_comm_group M'] [add_comm_group N']
variables [module R M] [module R N] [module R P] [module R M'] [module R N']
variables (bM : basis ι R M) (bN : basis κ R N) (bP : basis τ R P)
variables (bM' : basis ι' R M') (bN' : basis κ' R N')

open_locale kronecker
open matrix linear_map

/-- The linear map built from `tensor_product.map` corresponds to the matrix built from
`matrix.kronecker`. -/
lemma tensor_product.to_matrix_map (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
  to_matrix (bM.tensor_product bN) (bM'.tensor_product bN') (tensor_product.map f g)
    = to_matrix bM bM' f ⊗ₖ to_matrix bN bN' g :=
begin
  ext ⟨i, j⟩ ⟨i', j'⟩,
  simp_rw [matrix.kronecker_map_apply, to_matrix_apply, basis.tensor_product_apply,
    tensor_product.map_tmul, basis.tensor_product_repr_tmul_apply],
end

/-- The matrix built from `matrix.kronecker` corresponds to the linear map built from
`tensor_product.map`. -/
lemma matrix.to_lin_kronecker (A : matrix ι' ι R) (B : matrix κ' κ R) :
  to_lin (bM.tensor_product bN) (bM'.tensor_product bN') (A ⊗ₖ B) =
    tensor_product.map (to_lin bM bM' A) (to_lin bN bN' B) :=
by rw [←linear_equiv.eq_symm_apply, to_lin_symm, tensor_product.to_matrix_map,
  to_matrix_to_lin, to_matrix_to_lin]

/-- `tensor_product.comm` corresponds to a permutation of the identity matrix. -/
lemma tensor_product.to_matrix_comm :
  to_matrix (bM.tensor_product bN) (bN.tensor_product bM) (tensor_product.comm R M N)
    = (1 : matrix (ι × κ) (ι × κ) R).submatrix prod.swap id :=
begin
  ext ⟨i, j⟩ ⟨i', j'⟩,
  simp_rw [to_matrix_apply, basis.tensor_product_apply, linear_equiv.coe_coe,
    tensor_product.comm_tmul, basis.tensor_product_repr_tmul_apply, matrix.submatrix_apply,
    prod.swap_prod_mk, id.def, basis.repr_self_apply, matrix.one_apply, prod.ext_iff, ite_and,
    @eq_comm _ i', @eq_comm _ j'],
  split_ifs; simp,
end

/-- `tensor_product.assoc` corresponds to a permutation of the identity matrix. -/
lemma tensor_product.to_matrix_assoc :
  to_matrix ((bM.tensor_product bN).tensor_product bP) (bM.tensor_product (bN.tensor_product bP))
    (tensor_product.assoc R M N P)
    = (1 : matrix (ι × κ × τ) (ι × κ × τ) R).submatrix id (equiv.prod_assoc _ _ _) :=
begin
  ext ⟨i, j, k⟩ ⟨⟨i', j'⟩, k'⟩,
  simp_rw [to_matrix_apply, basis.tensor_product_apply, linear_equiv.coe_coe,
    tensor_product.assoc_tmul, basis.tensor_product_repr_tmul_apply, matrix.submatrix_apply,
    equiv.prod_assoc_apply, id.def, basis.repr_self_apply, matrix.one_apply, prod.ext_iff, ite_and,
    @eq_comm _ i', @eq_comm _ j', @eq_comm _ k'],
  split_ifs; simp,
end
