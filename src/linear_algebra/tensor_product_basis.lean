/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import linear_algebra.direct_sum.finsupp
import linear_algebra.finsupp_vector_space

/-!
# Bases and dimensionality of tensor products of modules

These can not go into `linear_algebra.tensor_product` since they depend on
`linear_algebra.finsupp_vector_space` which in turn imports `linear_algebra.tensor_product`.

-/
noncomputable theory
open set linear_map submodule

section comm_ring
variables {R : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
variables [comm_ring R] [add_comm_group M] [module R M] [add_comm_group N] [module R N]

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

end comm_ring
