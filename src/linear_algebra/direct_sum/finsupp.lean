/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import linear_algebra.finsupp
import linear_algebra.direct_sum.tensor_product

/-!
# Results on direct sums and finitely supported functions.

1. The linear equivalence between finitely supported functions `ι →₀ M` and
the direct sum of copies of `M` indexed by `ι`.

2. The tensor product of ι →₀ M and κ →₀ N is linearly equivalent to (ι × κ) →₀ (M ⊗ N).
-/

universes u v w

noncomputable theory
open_locale classical

open set linear_map submodule
variables {R : Type u} {M : Type v} {N : Type w} [ring R] [add_comm_group M] [module R M] [add_comm_group N] [module R N]

section finsupp_lequiv_direct_sum

variables (R M) (ι : Type*) [decidable_eq ι]

/-- The finitely supported functions ι →₀ M are in linear equivalence with the direct sum of
copies of M indexed by ι. -/
def finsupp_lequiv_direct_sum : (ι →₀ M) ≃ₗ[R] direct_sum ι (λ i, M) :=
linear_equiv.of_linear
  (finsupp.lsum $ direct_sum.lof R ι (λ _, M))
  (direct_sum.to_module _ _ _ finsupp.lsingle)
  (linear_map.ext $ direct_sum.to_module.ext _ $ λ i,
    linear_map.ext $ λ x, by simp [finsupp.sum_single_index])
  (linear_map.ext $ λ f, finsupp.ext $ λ i, by simp [finsupp.lsum_apply])

@[simp] theorem finsupp_lequiv_direct_sum_single (i : ι) (m : M) :
  finsupp_lequiv_direct_sum R M ι (finsupp.single i m) = direct_sum.lof R ι _ i m :=
finsupp.sum_single_index $ direct_sum.of_zero i

@[simp] theorem finsupp_lequiv_direct_sum_symm_lof (i : ι) (m : M) :
  (finsupp_lequiv_direct_sum R M ι).symm (direct_sum.lof R ι _ i m) = finsupp.single i m :=
direct_sum.to_module_lof _ _ _

end finsupp_lequiv_direct_sum

section tensor_product

open_locale tensor_product

/-- The tensor product of ι →₀ M and κ →₀ N is linearly equivalent to (ι × κ) →₀ (M ⊗ N). -/
def finsupp_tensor_finsupp (R M N ι κ : Sort*) [comm_ring R]
  [add_comm_group M] [module R M] [add_comm_group N] [module R N] :
  (ι →₀ M) ⊗[R] (κ →₀ N) ≃ₗ[R] (ι × κ) →₀ (M ⊗[R] N) :=
linear_equiv.trans
  (tensor_product.congr (finsupp_lequiv_direct_sum R M ι) (finsupp_lequiv_direct_sum R N κ)) $
linear_equiv.trans
  (tensor_product.direct_sum R ι κ (λ _, M) (λ _, N))
  (finsupp_lequiv_direct_sum R (M ⊗[R] N) (ι × κ)).symm

@[simp] theorem finsupp_tensor_finsupp_single (R M N ι κ : Sort*) [comm_ring R]
  [add_comm_group M] [module R M] [add_comm_group N] [module R N]
  (i : ι) (m : M) (k : κ) (n : N) :
  finsupp_tensor_finsupp R M N ι κ (finsupp.single i m ⊗ₜ finsupp.single k n) =
  finsupp.single (i, k) (m ⊗ₜ n) :=
by simp [finsupp_tensor_finsupp]

@[simp] theorem finsupp_tensor_finsupp_symm_single (R M N ι κ : Sort*) [comm_ring R]
  [add_comm_group M] [module R M] [add_comm_group N] [module R N]
  (i : ι × κ) (m : M) (n : N) :
  (finsupp_tensor_finsupp R M N ι κ).symm (finsupp.single i (m ⊗ₜ n)) =
  (finsupp.single i.1 m ⊗ₜ finsupp.single i.2 n) :=
prod.cases_on i $ λ i k, (linear_equiv.symm_apply_eq _).2
  (finsupp_tensor_finsupp_single _ _ _ _ _ _ _ _ _).symm

end tensor_product
