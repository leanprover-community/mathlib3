/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.multilinear.basic
import linear_algebra.tensor_product

/-!
# Constructions relating multilinear maps and tensor products.
-/

namespace multilinear_map

section dom_coprod

open_locale tensor_product

variables {R ι₁ ι₂ ι₃ ι₄ : Type*}
variables [comm_semiring R]
variables [decidable_eq ι₁] [decidable_eq ι₂][decidable_eq ι₃] [decidable_eq ι₄]
variables {N₁ : Type*} [add_comm_monoid N₁] [module R N₁]
variables {N₂ : Type*} [add_comm_monoid N₂] [module R N₂]
variables {N : Type*} [add_comm_monoid N] [module R N]

/-- Given two multilinear maps `(ι₁ → N) → N₁` and `(ι₂ → N) → N₂`, this produces the map
`(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂` by taking the coproduct of the domain and the tensor product
of the codomain.

This can be thought of as combining `equiv.sum_arrow_equiv_prod_arrow.symm` with
`tensor_product.map`, noting that the two operations can't be separated as the intermediate result
is not a `multilinear_map`.

While this can be generalized to work for dependent `Π i : ι₁, N'₁ i` instead of `ι₁ → N`, doing so
introduces `sum.elim N'₁ N'₂` types in the result which are difficult to work with and not defeq
to the simple case defined here. See [this zulip thread](
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Instances.20on.20.60sum.2Eelim.20A.20B.20i.60/near/218484619).
-/
@[simps apply]
def dom_coprod
  (a : multilinear_map R (λ _ : ι₁, N) N₁) (b : multilinear_map R (λ _ : ι₂, N) N₂) :
  multilinear_map R (λ _ : ι₁ ⊕ ι₂, N) (N₁ ⊗[R] N₂) :=
{ to_fun := λ v, a (λ i, v (sum.inl i)) ⊗ₜ b (λ i, v (sum.inr i)),
  map_add' := λ v i p q, by cases i; simp [tensor_product.add_tmul, tensor_product.tmul_add],
  map_smul' := λ v i c p, by cases i; simp [tensor_product.smul_tmul', tensor_product.tmul_smul] }

/-- A more bundled version of `multilinear_map.dom_coprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`. -/
def dom_coprod' :
  multilinear_map R (λ _ : ι₁, N) N₁ ⊗[R] multilinear_map R (λ _ : ι₂, N) N₂ →ₗ[R]
  multilinear_map R (λ _ : ι₁ ⊕ ι₂, N) (N₁ ⊗[R] N₂) :=
tensor_product.lift $ linear_map.mk₂ R (dom_coprod)
  (λ m₁ m₂ n, by { ext, simp only [dom_coprod_apply, tensor_product.add_tmul, add_apply] })
  (λ c m n,   by { ext, simp only [dom_coprod_apply, tensor_product.smul_tmul', smul_apply] })
  (λ m n₁ n₂, by { ext, simp only [dom_coprod_apply, tensor_product.tmul_add, add_apply] })
  (λ c m n,   by { ext, simp only [dom_coprod_apply, tensor_product.tmul_smul, smul_apply] })

@[simp]
lemma dom_coprod'_apply
  (a : multilinear_map R (λ _ : ι₁, N) N₁) (b : multilinear_map R (λ _ : ι₂, N) N₂) :
  dom_coprod' (a ⊗ₜ[R] b) = dom_coprod a b := rfl

/-- When passed an `equiv.sum_congr`, `multilinear_map.dom_dom_congr` distributes over
`multilinear_map.dom_coprod`. -/
lemma dom_coprod_dom_dom_congr_sum_congr
  (a : multilinear_map R (λ _ : ι₁, N) N₁) (b : multilinear_map R (λ _ : ι₂, N) N₂)
  (σa : ι₁ ≃ ι₃) (σb : ι₂ ≃ ι₄) :
    (a.dom_coprod b).dom_dom_congr (σa.sum_congr σb) =
      (a.dom_dom_congr σa).dom_coprod (b.dom_dom_congr σb) := rfl

end dom_coprod

end multilinear_map
