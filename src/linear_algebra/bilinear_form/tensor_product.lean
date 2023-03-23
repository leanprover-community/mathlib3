/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.bilinear_form
import linear_algebra.tensor_product
import linear_algebra.contraction

/-!
# The bilinear form on a tensor product

## Main definitions

* `bilin_form.tensor_distrib (B₁ ⊗ₜ B₂)`: the bilinear form on `M₁ ⊗ M₂` constructed by applying
  `B₁` on `M₁` and `B₂` on `M₂`.
* `bilin_form.tensor_distrib_equiv`: `bilin_form.tensor_distrib` as an equivalence on finite free
  modules.

-/

universes u v w
variables {ι : Type*} {R : Type*} {M₁ M₂ : Type*}

open_locale tensor_product

namespace bilin_form

section comm_semiring
variables [comm_semiring R]
variables [add_comm_monoid M₁] [add_comm_monoid M₂]
variables [module R M₁] [module R M₂]

/-- The tensor product of two bilinear forms injects into bilinear forms on tensor products. -/
def tensor_distrib : bilin_form R M₁ ⊗[R] bilin_form R M₂ →ₗ[R] bilin_form R (M₁ ⊗[R] M₂) :=
((tensor_product.tensor_tensor_tensor_comm R _ _ _ _).dual_map
  ≪≫ₗ (tensor_product.lift.equiv R _ _ _).symm
  ≪≫ₗ linear_map.to_bilin).to_linear_map
  ∘ₗ tensor_product.dual_distrib R _ _
  ∘ₗ (tensor_product.congr
    (bilin_form.to_lin ≪≫ₗ tensor_product.lift.equiv R _ _ _)
    (bilin_form.to_lin ≪≫ₗ tensor_product.lift.equiv R _ _ _)).to_linear_map

@[simp] lemma tensor_distrib_tmul (B₁ : bilin_form R M₁) (B₂ : bilin_form R M₂)
  (m₁ : M₁) (m₂ : M₂) (m₁' : M₁) (m₂' : M₂) :
  tensor_distrib (B₁ ⊗ₜ B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂') = B₁ m₁ m₁' * B₂ m₂ m₂' :=
rfl

/-- The tensor product of two bilinear forms, a shorthand for dot notation. -/
@[reducible]
protected def tmul (B₁ : bilin_form R M₁) (B₂ : bilin_form R M₂) : bilin_form R (M₁ ⊗[R] M₂) :=
tensor_distrib (B₁ ⊗ₜ[R] B₂)

end comm_semiring

section comm_ring
variables [comm_ring R]
variables [add_comm_group M₁] [add_comm_group M₂]
variables [module R M₁] [module R M₂]
variables [module.free R M₁] [module.finite R M₁]
variables [module.free R M₂] [module.finite R M₂]
variables [nontrivial R]

/-- `tensor_distrib` as an equivalence. -/
noncomputable def tensor_distrib_equiv :
  bilin_form R M₁ ⊗[R] bilin_form R M₂ ≃ₗ[R] bilin_form R (M₁ ⊗[R] M₂) :=
-- the same `linear_equiv`s as from `tensor_distrib`, but with the inner linear map also as an
-- equiv
tensor_product.congr
    (bilin_form.to_lin ≪≫ₗ tensor_product.lift.equiv R _ _ _)
    (bilin_form.to_lin ≪≫ₗ tensor_product.lift.equiv R _ _ _)
  ≪≫ₗ tensor_product.dual_distrib_equiv R (M₁ ⊗ M₁) (M₂ ⊗ M₂)
  ≪≫ₗ (tensor_product.tensor_tensor_tensor_comm R _ _ _ _).dual_map
  ≪≫ₗ (tensor_product.lift.equiv R _ _ _).symm
  ≪≫ₗ linear_map.to_bilin

@[simp]
lemma tensor_distrib_equiv_apply (B : bilin_form R M₁ ⊗ bilin_form R M₂) :
  tensor_distrib_equiv B = tensor_distrib B := rfl

end comm_ring

end bilin_form
