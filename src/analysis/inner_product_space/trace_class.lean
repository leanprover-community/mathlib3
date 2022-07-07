/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.inner_product_space.basic

/-!
# Trace Class

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open tensor_product
open_locale tensor_product

section finite_rank

def finite_rank_operator_submodule {𝕜₁ 𝕜₂ : Type*} [semiring 𝕜₁] [field 𝕜₂]
  (σ₁₂ : 𝕜₁ →+* 𝕜₂) [ring_hom_surjective σ₁₂] (E F : Type*) [add_comm_monoid E]
  [add_comm_group F] [module 𝕜₁ E] [module 𝕜₂ F] [topological_space E] [topological_space F]
  [has_continuous_add F] [has_continuous_const_smul 𝕜₂ F] : submodule 𝕜₂ (E →SL[σ₁₂] F) :=
{ carrier := {f | finite_dimensional 𝕜₂ f.range},
  zero_mem' :=
  begin
    change finite_dimensional 𝕜₂ (0 : E →ₛₗ[σ₁₂] F).range,
    rw linear_map.range_zero,
    exact finite_dimensional_bot _ _
  end,
  add_mem' := λ f g (hf : finite_dimensional _ _) (hg : finite_dimensional _ _),
  begin
    change finite_dimensional _ _,
    rw [continuous_linear_map.range, linear_map.range_eq_map] at *,
    haveI := hf,
    haveI := hg,
    exact submodule.finite_dimensional_of_le ((⊤ : submodule 𝕜₁ E).map_add_le f g)
  end,
  smul_mem' := λ a f (hf : finite_dimensional _ _),
  begin
    change finite_dimensional _ _,
    rw [continuous_linear_map.range, linear_map.range_eq_map] at *,
    by_cases ha : a = 0,
    { rw [ha, zero_smul _ f, continuous_linear_map.coe_zero, submodule.map_zero],
      exact finite_dimensional_bot _ _ },
    { rwa [continuous_linear_map.coe_smul, submodule.map_smul _ _ _ ha] }
  end }

def finite_rank_operator {𝕜₁ 𝕜₂ : Type*} [semiring 𝕜₁] [field 𝕜₂]
  (σ₁₂ : 𝕜₁ →+* 𝕜₂) [ring_hom_surjective σ₁₂] (E F : Type*) [add_comm_monoid E]
  [add_comm_group F] [module 𝕜₁ E] [module 𝕜₂ F] [topological_space E] [topological_space F]
  [has_continuous_add F] [has_continuous_const_smul 𝕜₂ F] : Type* :=
finite_rank_operator_submodule σ₁₂ E F

namespace finite_rank_operator

section basics

variables {S R K : Type*} [semiring S] [ring R] [field K] {σₛ : S →+* K} {σ : R →+* K}
  [ring_hom_surjective σₛ] [ring_hom_surjective σ] {E F G : Type*} [add_comm_monoid E]
  [add_comm_group F] [add_comm_group G] [module S E] [module R E] [module K F] [module K G]
  [topological_space E] [topological_space F] [topological_space G]
  [has_continuous_const_smul K F] [has_continuous_const_smul K G]

instance [has_continuous_add F] : add_comm_monoid (finite_rank_operator σₛ E F) :=
submodule.add_comm_monoid _

instance [topological_add_group F] : add_comm_group (finite_rank_operator σ E F) :=
submodule.add_comm_group _

instance [has_continuous_add F] : module K (finite_rank_operator σₛ E F) :=
submodule.module _

def smul_right [module K E] [topological_space K] [has_continuous_add F] [has_continuous_smul K F]
  (l : E →L[K] K) (x : F) : (finite_rank_operator (ring_hom.id K) E F) :=
⟨l.smul_right x, _⟩

def smul_right [module K E] [topological_space K] [topological_ring K] [has_continuous_add F] :
  (E →L[K] K) →ₗ[K] F →ₗ[K] (finite_rank_operator (ring_hom.id K) E F) :=
{  }

variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜] (E G) [module 𝕜 E] [module 𝕜 G]

def dual_tensor_hom [has_continuous_add G] [has_continuous_const_smul 𝕜 G] :
  ((E →L[𝕜] 𝕜) ⊗[𝕜] G) →ₗ[𝕜] (finite_rank_operator (ring_hom.id 𝕜) E G) :=
let E' := E →L[𝕜] 𝕜 in
  (uncurry 𝕜 E' G (finite_rank_operator (ring_hom.id 𝕜) E G) : _ → E' ⊗[𝕜] G →ₗ[𝕜] (finite_rank_operator (ring_hom.id 𝕜) E G))
  _

variables

end basics

end finite_rank_operator

end finite_rank
