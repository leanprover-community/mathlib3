/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import data.matrix.kronecker
import linear_algebra.direct_sum.finsupp
import linear_algebra.finsupp_vector_space
import linear_algebra.matrix.to_lin

/-!
# Bases and dimensionality of tensor products of modules

These can not go into `linear_algebra.tensor_product` since they depend on
`linear_algebra.finsupp_vector_space` which in turn imports `linear_algebra.tensor_product`.

-/
noncomputable theory
open set linear_map submodule
open_locale tensor_product

section comm_ring
variables {R : Type*} {M N M' N' : Type*} {ι κ ι' κ' : Type*}
variables [comm_ring R]
variables [add_comm_group M] [add_comm_group N] [add_comm_group M'] [add_comm_group N']
variables [module R M] [module R N] [module R M'] [module R N']

/-- If b : ι → M and c : κ → N are bases then so is λ i, b i.1 ⊗ₜ c i.2 : ι × κ → M ⊗ N. -/
def basis.tensor_product (b : basis ι R M) (c : basis κ R N) :
  basis (ι × κ) R (tensor_product R M N) :=
finsupp.basis_single_one.map
  ((tensor_product.congr b.repr c.repr).trans $
    (finsupp_tensor_finsupp R _ _ _ _).trans $
    finsupp.lcongr (equiv.refl _) (tensor_product.lid R R)).symm

@[simp]
lemma basis.tensor_product_apply (b : basis ι R M) (c : basis κ R N) (i : ι) (j : κ) :
  basis.tensor_product b c (i, j) = b i ⊗ₜ c j :=
by simp [basis.tensor_product]

lemma basis.tensor_product_apply' (b : basis ι R M) (c : basis κ R N) (i : ι × κ) :
  basis.tensor_product b c i = b i.1 ⊗ₜ c i.2 :=
by simp [basis.tensor_product]

@[simp]
lemma basis.tensor_product_repr_tmul_apply (b : basis ι R M) (c : basis κ R N)
  (m : M) (n : N) (i : ι) (j : κ) :
  (basis.tensor_product b c).repr (m ⊗ₜ n) (i, j) = b.repr m i * c.repr n j :=
by simp [basis.tensor_product]

open_locale kronecker

/-!
### The link between `basis.tensor_product` and `matrix.kronecker`
-/

section matrix
variables
  [decidable_eq ι] [decidable_eq κ] [decidable_eq ι'] [decidable_eq κ']
  [fintype ι] [fintype κ] [fintype ι'] [fintype κ']
  (bM : basis ι R M) (bN : basis κ R N) (bM' : basis ι' R M') (bN' : basis κ' R N')

lemma tensor_product.to_matrix_map (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
  linear_map.to_matrix (bM.tensor_product bN) (bM'.tensor_product bN') (tensor_product.map f g)
    = linear_map.to_matrix bM bM' f ⊗ₖ linear_map.to_matrix bN bN' g :=
begin
  ext ⟨i, j⟩ ⟨i', j'⟩,
  simp_rw [matrix.kronecker_map, to_matrix_apply, basis.tensor_product_apply,
    tensor_product.map_tmul, basis.tensor_product_repr_tmul_apply],
end

lemma matrix.to_lin_kronecker (A : matrix ι' ι R) (B : matrix κ' κ R) :
  matrix.to_lin (bM.tensor_product bN) (bM'.tensor_product bN') (A ⊗ₖ B) =
    tensor_product.map (matrix.to_lin bM bM' A) (matrix.to_lin bN bN' B) :=
by rw [←linear_equiv.eq_symm_apply, matrix.to_lin_symm, tensor_product.to_matrix_map,
  to_matrix_to_lin, to_matrix_to_lin]

end matrix

end comm_ring
