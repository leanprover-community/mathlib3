/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import data.matrix.kronecker
import linear_algebra.matrix.to_lin
import linear_algebra.tensor_product.basis

/-!
# The link between `tensor_product.map` and `matrix.kronecker`

Taking the tensor product of linear maps is equivalent to taking the kronecker product of their
matrix representations, via `basis.tensor_product`.
-/

variables {R : Type*} {M N M' N' : Type*} {ι κ ι' κ' : Type*}
variables [decidable_eq ι] [decidable_eq κ]
variables [fintype ι] [fintype κ] [fintype ι'] [fintype κ']
variables [comm_ring R]
variables [add_comm_group M] [add_comm_group N] [add_comm_group M'] [add_comm_group N']
variables [module R M] [module R N] [module R M'] [module R N']
variables (bM : basis ι R M) (bN : basis κ R N) (bM' : basis ι' R M') (bN' : basis κ' R N')

open_locale kronecker
open matrix linear_map

/-- The linear map built from `tensor_product.map` corresponds to the matrix built from
`matrix.kronecker`. -/
lemma tensor_product.to_matrix_map (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
  to_matrix (bM.tensor_product bN) (bM'.tensor_product bN') (tensor_product.map f g)
    = to_matrix bM bM' f ⊗ₖ to_matrix bN bN' g :=
begin
  ext ⟨i, j⟩ ⟨i', j'⟩,
  simp_rw [matrix.kronecker_map, to_matrix_apply, basis.tensor_product_apply,
    tensor_product.map_tmul, basis.tensor_product_repr_tmul_apply],
end

/-- The matrix built from `matrix.kronecker` corresponds to the linear map built from
`tensor_product.map`. -/
lemma matrix.to_lin_kronecker (A : matrix ι' ι R) (B : matrix κ' κ R) :
  to_lin (bM.tensor_product bN) (bM'.tensor_product bN') (A ⊗ₖ B) =
    tensor_product.map (to_lin bM bM' A) (to_lin bN bN' B) :=
by rw [←linear_equiv.eq_symm_apply, to_lin_symm, tensor_product.to_matrix_map,
  to_matrix_to_lin, to_matrix_to_lin]
