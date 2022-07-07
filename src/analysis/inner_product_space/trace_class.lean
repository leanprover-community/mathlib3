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

#check submodule.finite_dimensional_sup

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
    { rw [continuous_linear_map.coe_smul, submodule.map_smul f ⊤ _ ha], }
  end }
