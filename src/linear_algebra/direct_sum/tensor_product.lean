/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Eric Wieser
-/

import linear_algebra.tensor_product
import algebra.direct_sum.module

/-!
# Tensor products of direct sums

This file shows that taking `tensor_product`s commutes with taking `direct_sum`s in both arguments.

## Main results

* `tensor_product.direct_sum`
* `tensor_product.direct_sum_left`
* `tensor_product.direct_sum_right`
-/

section ring

namespace tensor_product

open_locale tensor_product
open_locale direct_sum
open linear_map
local attribute [ext] tensor_product.ext

variables (R : Type*) [comm_ring R]
variables {ι₁ : Type*} {ι₂ : Type*}
variables [decidable_eq ι₁] [decidable_eq ι₂]
variables (M₁ : ι₁ → Type*) (M₁' : Type*) (M₂ : ι₂ → Type*) (M₂' : Type*)
variables [Π i₁, add_comm_group (M₁ i₁)] [add_comm_group M₁']
variables [Π i₂, add_comm_group (M₂ i₂)] [add_comm_group M₂']
variables [Π i₁, module R (M₁ i₁)] [module R M₁'] [Π i₂, module R (M₂ i₂)] [module R M₂']

/-- The linear equivalence `(⨁ i₁, M₁ i₁) ⊗ (⨁ i₂, M₂ i₂) ≃ (⨁ i₁, ⨁ i₂, M₁ i₁ ⊗ M₂ i₂)`, i.e.
"tensor product distributes over direct sum". -/
protected def direct_sum :
  (⨁ i₁, M₁ i₁) ⊗[R] (⨁ i₂, M₂ i₂) ≃ₗ[R] (⨁ (i : ι₁ × ι₂), M₁ i.1 ⊗[R] M₂ i.2) :=
begin
  refine linear_equiv.of_linear
    (lift $ direct_sum.to_module R _ _ $ λ i₁, flip $ direct_sum.to_module R _ _ $ λ i₂,
      flip $ curry $ direct_sum.lof R (ι₁ × ι₂) (λ i, M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂))
    (direct_sum.to_module R _ _ $ λ i, map (direct_sum.lof R _ _ _) (direct_sum.lof R _ _ _))
    _ _; [ext ⟨i₁, i₂⟩ x₁ x₂ : 4, ext i₁ i₂ x₁ x₂ : 5],
  repeat { rw compr₂_apply <|> rw comp_apply <|> rw id_apply <|> rw mk_apply <|>
    rw direct_sum.to_module_lof <|> rw map_tmul <|> rw lift.tmul <|> rw flip_apply <|>
    rw curry_apply },
end

/-- Tensor products distribute over a direct sum on the left . -/
def direct_sum_left : (⨁ i₁, M₁ i₁) ⊗[R] M₂' ≃ₗ[R] (⨁ i, M₁ i ⊗[R] M₂') :=
linear_equiv.of_linear
  (lift $ direct_sum.to_module R _ _ $ λ i, (mk R _ _).compr₂ $
    (direct_sum.lof R ι₁ (λ i, M₁ i ⊗[R] M₂') _))
  (direct_sum.to_module R _ _ $ λ i, rtensor _ (direct_sum.lof R ι₁ _ _))
  (direct_sum.linear_map_ext R $ λ i, tensor_product.ext $ linear_map.ext₂ $ λ m₁ m₂, begin
    dsimp only [comp_apply, compr₂_apply, id_apply, mk_apply],
    simp_rw [direct_sum.to_module_lof, rtensor_tmul, lift.tmul, direct_sum.to_module_lof,
      compr₂_apply, mk_apply],
  end)
  (tensor_product.ext $ direct_sum.linear_map_ext R $ λ i, linear_map.ext₂ $ λ m₁ m₂, begin
    dsimp only [comp_apply, compr₂_apply, id_apply, mk_apply],
    simp_rw [direct_sum.to_module_lof, lift.tmul, direct_sum.to_module_lof, compr₂_apply, mk_apply,
      direct_sum.to_module_lof, rtensor_tmul],
  end)

/-- Tensor products distribute over a direct sum on the right. -/
def direct_sum_right : M₁' ⊗[R] (⨁ i, M₂ i) ≃ₗ[R] (⨁ i, M₁' ⊗[R] M₂ i) :=
(tensor_product.comm R _ _) ≪≫ₗ (direct_sum_left R M₂ M₁') ≪≫ₗ
  (dfinsupp.map_range.linear_equiv $ λ i, (tensor_product.comm R _ _))

variables {M₁ M₁' M₂ M₂'}

@[simp] theorem direct_sum_lof_tmul_lof (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) :
  tensor_product.direct_sum R M₁ M₂ (direct_sum.lof R ι₁ M₁ i₁ m₁ ⊗ₜ direct_sum.lof R ι₂ M₂ i₂ m₂) =
    direct_sum.lof R (ι₁ × ι₂) (λ i, M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂) (m₁ ⊗ₜ m₂) :=
by simp [tensor_product.direct_sum]

@[simp] lemma direct_sum_left_tmul_lof (i : ι₁) (x : M₁ i) (y : M₂') :
  direct_sum_left R M₁ M₂' (direct_sum.lof R _ _ i x ⊗ₜ[R] y)
    = direct_sum.lof R _ _ i (x ⊗ₜ[R] y) :=
begin
  dsimp only [direct_sum_left, linear_equiv.of_linear_apply, lift.tmul],
  rw direct_sum.to_module_lof R i,
  refl,
end

@[simp] lemma direct_sum_left_symm_lof_tmul (i : ι₁) (x : M₁ i) (y : M₂') :
  (direct_sum_left R M₁ M₂').symm (direct_sum.lof R _ _ i (x ⊗ₜ[R] y))
    = direct_sum.lof R _ _ i x ⊗ₜ[R] y :=
by rw [linear_equiv.symm_apply_eq, direct_sum_left_tmul_lof]

@[simp] lemma direct_sum_right_tmul_lof (x : M₁') (i : ι₂) (y : M₂ i) :
  direct_sum_right R M₁' M₂ (x ⊗ₜ[R] direct_sum.lof R _ _ i y)
    = direct_sum.lof R _ _ i (x ⊗ₜ[R] y) :=
begin
  dsimp only [direct_sum_right, linear_equiv.trans_apply, tensor_product.comm_tmul],
  rw direct_sum_left_tmul_lof,
  exact dfinsupp.map_range_single,
end

@[simp] lemma direct_sum_right_symm_lof_tmul (x : M₁') (i : ι₂) (y : M₂ i):
  (direct_sum_right R M₁' M₂).symm (direct_sum.lof R _ _ i (x ⊗ₜ[R] y))
    = x ⊗ₜ[R] direct_sum.lof R _ _ i y :=
by rw [linear_equiv.symm_apply_eq, direct_sum_right_tmul_lof]

end tensor_product

end ring
