/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.algebra.uniform_convergence

/-!
# Strong Topology

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

namespace continuous_linear_map

section general

variables {𝕜₁ 𝕜₂ : Type*} [normed_field 𝕜₁] [normed_field 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂)
  (E F : Type*) [add_comm_group E] [module 𝕜₁ E]
  [add_comm_group F] [module 𝕜₂ F] [topological_space E]

def strong_topology [topological_space F] [topological_add_group F]
  (𝔖 : set $ set E) :
  topological_space (E →SL[σ] F) :=
(@uniform_convergence_on.topological_space E F
  (topological_add_group.to_uniform_space F) 𝔖).induced coe_fn

-- Meh, TODO: find a better name
def strong_uniformity [uniform_space F] [uniform_add_group F]
  (𝔖 : set (set E)) : uniform_space (E →SL[σ] F) :=
@uniform_space.replace_topology _ (strong_topology σ E F 𝔖)
  ((uniform_convergence_on.uniform_space E F 𝔖).comap coe_fn)
  (by rw [strong_topology, uniform_add_group.to_uniform_space_eq]; refl)

@[simp] lemma strong_uniformity_topology_eq [uniform_space F] [uniform_add_group F]
  (𝔖 : set (set E)) :
  (strong_uniformity σ E F 𝔖).to_topological_space = strong_topology σ E F 𝔖 :=
rfl

lemma strong_uniformity.uniform_add_group [uniform_space F] [uniform_add_group F]
  (𝔖 : set $ set E) : @uniform_add_group _ (strong_uniformity σ E F 𝔖) _ :=
begin
  letI : uniform_space (E → F) := uniform_convergence_on.uniform_space E F 𝔖,
  letI : uniform_space (E →SL[σ] F) := strong_uniformity σ E F 𝔖,
  haveI : uniform_add_group (E → F) := uniform_convergence_on.uniform_add_group,
  rw [strong_uniformity, uniform_space.replace_topology_eq],
  let φ : (E →SL[σ] F) →+ E → F := ⟨(coe_fn : (E →SL[σ] F) → E → F), rfl, λ _ _, rfl⟩,
  exact uniform_add_group_comap φ
end

lemma strong_topology.topological_add_group [topological_space F] [topological_add_group F]
  (𝔖 : set $ set E) :
  @topological_add_group (E →SL[σ] F) (strong_topology σ E F 𝔖) _ :=
begin
  letI : uniform_space F := topological_add_group.to_uniform_space F,
  haveI : uniform_add_group F := topological_add_group_is_uniform,
  letI : uniform_space (E →SL[σ] F) := strong_uniformity σ E F 𝔖,
  haveI : uniform_add_group (E →SL[σ] F) := strong_uniformity.uniform_add_group σ E F 𝔖,
  apply_instance
end

lemma strong_topology.has_continuous_smul [ring_hom_surjective σ] [ring_hom_isometric σ]
  [topological_space F] [topological_add_group F] [has_continuous_smul 𝕜₂ F] (𝔖 : set $ set E)
  (h𝔖₁ : 𝔖.nonempty) (h𝔖₂ : directed_on (⊆) 𝔖) (h𝔖₃ : ∀ S ∈ 𝔖, bornology.is_vonN_bounded 𝕜₁ S) :
  @has_continuous_smul 𝕜₂ (E →SL[σ] F) _ _ (strong_topology σ E F 𝔖) :=
begin
  letI : uniform_space F := topological_add_group.to_uniform_space F,
  haveI : uniform_add_group F := topological_add_group_is_uniform,
  letI : topological_space (E → F) := uniform_convergence_on.topological_space E F 𝔖,
  letI : topological_space (E →SL[σ] F) := strong_topology σ E F 𝔖,
  let φ : (E →SL[σ] F) →ₗ[𝕜₂] E → F := ⟨(coe_fn : (E →SL[σ] F) → E → F), λ _ _, rfl, λ _ _, rfl⟩,
  exact uniform_convergence_on.has_continuous_smul_induced_of_image_bounded 𝕜₂ E F (E →SL[σ] F)
    h𝔖₁ h𝔖₂ φ ⟨rfl⟩ (λ u s hs, (h𝔖₃ s hs).image u)
end

end general

section bounded_sets

variables {𝕜₁ 𝕜₂ : Type*} [normed_field 𝕜₁] [normed_field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E F : Type*}
  [add_comm_group E] [module 𝕜₁ E] [add_comm_group F] [module 𝕜₂ F] [topological_space E]

instance [topological_space F] [topological_add_group F] : topological_space (E →SL[σ] F) :=
strong_topology σ E F {S | bornology.is_vonN_bounded 𝕜₁ S}

instance [topological_space F] [topological_add_group F] : topological_add_group (E →SL[σ] F) :=
strong_topology.topological_add_group σ E F _

instance [ring_hom_surjective σ] [ring_hom_isometric σ] [topological_space F]
  [topological_add_group F] [has_continuous_smul 𝕜₂ F] :
  has_continuous_smul 𝕜₂ (E →SL[σ] F) :=
strong_topology.has_continuous_smul σ E F {S | bornology.is_vonN_bounded 𝕜₁ S}
  ⟨∅, bornology.is_vonN_bounded_empty 𝕜₁ E⟩
  (λ s₁ h₁ s₂ h₂, ⟨s₁ ∪ s₂, h₁.union h₂, s₁.subset_union_left s₂, s₁.subset_union_right s₂⟩)
  (λ s hs, hs)

instance [uniform_space F] [uniform_add_group F] : uniform_space (E →SL[σ] F) :=
strong_uniformity σ E F {S | bornology.is_vonN_bounded 𝕜₁ S}

instance [uniform_space F] [uniform_add_group F] : uniform_add_group (E →SL[σ] F) :=
strong_uniformity.uniform_add_group σ E F _

end bounded_sets

end continuous_linear_map
