/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import algebra.direct_sum.finsupp
import linear_algebra.finsupp
import linear_algebra.direct_sum.tensor_product
import data.finsupp.to_dfinsupp

/-!
# Results on finitely supported functions.

The tensor product of ι →₀ M and κ →₀ N is linearly equivalent to (ι × κ) →₀ (M ⊗ N).
-/

universes u v w

noncomputable theory
open_locale direct_sum

open set linear_map submodule
variables {R : Type u} {M : Type v} {N : Type w} [ring R] [add_comm_group M] [module R M]
  [add_comm_group N] [module R N]

section tensor_product

open tensor_product
open_locale tensor_product classical

/-- The tensor product of ι →₀ M and κ →₀ N is linearly equivalent to (ι × κ) →₀ (M ⊗ N). -/
def finsupp_tensor_finsupp (R M N ι κ : Sort*) [comm_ring R]
  [add_comm_group M] [module R M] [add_comm_group N] [module R N] :
  (ι →₀ M) ⊗[R] (κ →₀ N) ≃ₗ[R] (ι × κ) →₀ (M ⊗[R] N) :=
(tensor_product.congr (finsupp_lequiv_direct_sum R M ι) (finsupp_lequiv_direct_sum R N κ))
  ≪≫ₗ ((tensor_product.direct_sum R ι κ (λ _, M) (λ _, N))
  ≪≫ₗ (finsupp_lequiv_direct_sum R (M ⊗[R] N) (ι × κ)).symm)

@[simp] theorem finsupp_tensor_finsupp_single (R M N ι κ : Sort*) [comm_ring R]
  [add_comm_group M] [module R M] [add_comm_group N] [module R N]
  (i : ι) (m : M) (k : κ) (n : N) :
  finsupp_tensor_finsupp R M N ι κ (finsupp.single i m ⊗ₜ finsupp.single k n) =
  finsupp.single (i, k) (m ⊗ₜ n) :=
by simp [finsupp_tensor_finsupp]

@[simp] theorem finsupp_tensor_finsupp_apply (R M N ι κ : Sort*) [comm_ring R]
  [add_comm_group M] [module R M] [add_comm_group N] [module R N]
  (f : ι →₀ M) (g : κ →₀ N) (i : ι) (k : κ) :
  finsupp_tensor_finsupp R M N ι κ (f ⊗ₜ g) (i, k) = f i ⊗ₜ g k :=
begin
  apply finsupp.induction_linear f,
  { simp, },
  { intros f₁ f₂ hf₁ hf₂, simp [add_tmul, hf₁, hf₂], },
  { intros i' m,
    apply finsupp.induction_linear g,
    { simp, },
    { intros g₁ g₂ hg₁ hg₂, simp [tmul_add, hg₁, hg₂], },
    { intros k' n,
      simp only [finsupp_tensor_finsupp_single],
      simp only [finsupp.single, finsupp.coe_mk],
      split_ifs; finish, } }
end

@[simp] theorem finsupp_tensor_finsupp_symm_single (R M N ι κ : Sort*) [comm_ring R]
  [add_comm_group M] [module R M] [add_comm_group N] [module R N]
  (i : ι × κ) (m : M) (n : N) :
  (finsupp_tensor_finsupp R M N ι κ).symm (finsupp.single i (m ⊗ₜ n)) =
  (finsupp.single i.1 m ⊗ₜ finsupp.single i.2 n) :=
prod.cases_on i $ λ i k, (linear_equiv.symm_apply_eq _).2
  (finsupp_tensor_finsupp_single _ _ _ _ _ _ _ _ _).symm

variables (S : Type*) [comm_ring S] (α β : Type*)

/--
A variant of `finsupp_tensor_finsupp` where both modules are the ground ring.
-/
def finsupp_tensor_finsupp' : ((α →₀ S) ⊗[S] (β →₀ S)) ≃ₗ[S] (α × β →₀ S) :=
(finsupp_tensor_finsupp S S S α β).trans (finsupp.lcongr (equiv.refl _) (tensor_product.lid S S))

@[simp] lemma finsupp_tensor_finsupp'_apply_apply (f : α →₀ S) (g : β →₀ S) (a : α) (b : β) :
  finsupp_tensor_finsupp' S α β (f ⊗ₜ[S] g) (a, b) = f a * g b :=
by simp [finsupp_tensor_finsupp']

@[simp] lemma finsupp_tensor_finsupp'_single_tmul_single (a : α) (b : β) (r₁ r₂ : S) :
  finsupp_tensor_finsupp' S α β (finsupp.single a r₁ ⊗ₜ[S] finsupp.single b r₂) =
    finsupp.single (a, b) (r₁ * r₂) :=
by { ext ⟨a', b'⟩, simp [finsupp.single], split_ifs; finish }

end tensor_product
