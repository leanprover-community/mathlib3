/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.bilinear_form
import linear_algebra.tensor_product
import linear_algebra.contraction

/-! # Bilinear form on tensor product

## Main definitions

* `bilin_form.tmul Q₁ Q₂`: the bilinear form constructed elementwise on a tensor product

-/

universes u v w
variables {ι : Type*} {R : Type*} {M₁ M₂ : Type*}

open_locale tensor_product

namespace bilin_form


section comm_semiring
variables [comm_semiring R]
variables [add_comm_monoid M₁] [add_comm_monoid M₂]
variables [module R M₁] [module R M₂]

/-- The tensor product of two bilinear forms. -/
def tensor_distrib : bilin_form R M₁ ⊗[R] bilin_form R M₂ →ₗ[R] bilin_form R (M₁ ⊗[R] M₂) :=
linear_map.to_bilin.to_linear_map
  ∘ₗ tensor_product.lcurry R _ _ _
  ∘ₗ (tensor_product.tensor_tensor_tensor_comm R _ _ _ _).to_linear_map.dual_map
  ∘ₗ tensor_product.dual_distrib R _ _
  ∘ₗ tensor_product.map
    (tensor_product.uncurry R _ _ _ ∘ₗ bilin_form.to_lin.to_linear_map)
    (tensor_product.uncurry R _ _ _ ∘ₗ bilin_form.to_lin.to_linear_map)

/-- The tensor product of two bilinear forms. -/
protected def tmul (B₁ : bilin_form R M₁) (B₂ : bilin_form R M₂) : bilin_form R (M₁ ⊗[R] M₂) :=
tensor_distrib (B₁ ⊗ₜ[R] B₂)

@[simp] lemma tmul_tmul (B₁ : bilin_form R M₁) (B₂ : bilin_form R M₂)
  (m₁ m₁' : M₁) (m₂ m₂' : M₂) :
  B₁.tmul B₂ (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂') = B₁ m₁ m₁' * B₂ m₂ m₂' :=
rfl

end comm_semiring

section comm_ring
variables [comm_ring R]
variables [add_comm_group M₁] [add_comm_group M₂]
variables [module R M₁] [module R M₂]
variables [module.free R M₁] [module.finite R M₁]
variables [module.free R M₂] [module.finite R M₂]
variables [nontrivial R]

noncomputable def tmul_equiv :
  bilin_form R M₁ ⊗[R] bilin_form R M₂ ≃ₗ[R] bilin_form R (M₁ ⊗[R] M₂) :=
begin
  -- convert to bilinear maps
  refine (tensor_product.congr linear_map.to_bilin linear_map.to_bilin).symm
    ≪≫ₗ _ ≪≫ₗ linear_map.to_bilin,
  -- convert to tnsor products
  refine (tensor_product.congr (tensor_product.lift.equiv R M₁ M₁ R)
                               (tensor_product.lift.equiv R M₂ M₂ R))
    ≪≫ₗ _ ≪≫ₗ (tensor_product.lift.equiv R (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₂) R).symm,
  -- reassociate
  refine _ ≪≫ₗ
    (tensor_product.tensor_tensor_tensor_comm R _ _ _ _).arrow_congr (tensor_product.lid R R),
  exact hom_tensor_hom_equiv R _ _ R R
end

lemma tmul_equiv_tmul (B₁ : bilin_form R M₁) (B₂ : bilin_form R M₂) :
  tmul_equiv (B₁ ⊗ₜ[R] B₂) = B₁.tmul B₂ :=
begin
  -- the definition of `hom_tensor_hom_equiv` means this can't just be rfl :(
  dsimp [tmul_equiv, bilin_form.tmul, tensor_product.lift.equiv_apply,
    linear_equiv.arrow_congr_apply],
  refine congr_arg _ _,
  refine congr_arg _ _,
  apply tensor_product.ext_fourfold',
  dsimp [tensor_product.lift.equiv_apply,
    tensor_product.tensor_tensor_tensor_comm_symm],
  rw hom_tensor_hom_equiv_apply _,
  sorry
end

end comm_ring

end bilin_form
