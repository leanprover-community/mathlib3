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

variables (𝕜 E F : Type*) [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
  [add_comm_group F] [module 𝕜 F] [topological_space E]

def strong_topology [topological_space F] [topological_add_group F]
  (𝔖 : set $ set E) :
  topological_space (E →L[𝕜] F) :=
(@uniform_convergence_on.topological_space E F
  (topological_add_group.to_uniform_space F) 𝔖).induced coe_fn

-- Meh, TODO: find a better name
def strong_uniformity [uniform_space F] [uniform_add_group F]
  (𝔖 : set (set E)) : uniform_space (E →L[𝕜] F) :=
@uniform_space.replace_topology _ (strong_topology 𝕜 E F 𝔖)
  ((uniform_convergence_on.uniform_space E F 𝔖).comap coe_fn)
  (by rw [strong_topology, uniform_add_group.to_uniform_space_eq]; refl)

@[simp] lemma strong_uniformity_topology_eq [uniform_space F] [uniform_add_group F]
  (𝔖 : set (set E)) :
  (strong_uniformity 𝕜 E F 𝔖).to_topological_space = strong_topology 𝕜 E F 𝔖 :=
rfl

lemma strong_uniformity.uniform_add_group [uniform_space F] [uniform_add_group F]
  (𝔖 : set $ set E) : @uniform_add_group _ (strong_uniformity 𝕜 E F 𝔖) _ :=
begin
  letI : uniform_space (E → F) := uniform_convergence_on.uniform_space E F 𝔖,
  letI : uniform_space (E →L[𝕜] F) := strong_uniformity 𝕜 E F 𝔖,
  haveI : uniform_add_group (E → F) := uniform_convergence_on.uniform_add_group,
  rw [strong_uniformity, uniform_space.replace_topology_eq],
  let φ : (E →L[𝕜] F) →+ E → F := ⟨(coe_fn : (E →L[𝕜] F) → E → F), rfl, λ _ _, rfl⟩,
  exact uniform_add_group_comap φ
end

lemma strong_topology.topological_add_group [topological_space F] [topological_add_group F]
  (𝔖 : set $ set E) :
  @topological_add_group (E →L[𝕜] F) (strong_topology 𝕜 E F 𝔖) _ :=
begin
  letI : uniform_space F := topological_add_group.to_uniform_space F,
  haveI : uniform_add_group F := topological_add_group_is_uniform,
  letI : uniform_space (E →L[𝕜] F) := strong_uniformity 𝕜 E F 𝔖,
  haveI : uniform_add_group (E →L[𝕜] F) := strong_uniformity.uniform_add_group 𝕜 E F 𝔖,
  apply_instance
end

lemma strong_topology.has_continuous_smul [topological_space F] [topological_add_group F]
  [has_continuous_smul 𝕜 F] (𝔖 : set $ set E) (h𝔖₁ : 𝔖.nonempty) (h𝔖₂ : directed_on (⊆) 𝔖)
  (h𝔖₃ : ∀ S ∈ 𝔖, bornology.is_vonN_bounded 𝕜 S) :
  @has_continuous_smul 𝕜 (E →L[𝕜] F) _ _ (strong_topology 𝕜 E F 𝔖) :=
begin

  letI : uniform_space F := topological_add_group.to_uniform_space F,
  letI : uniform_space (E → F) := uniform_convergence_on.uniform_space E F 𝔖,
  haveI : has_continuous_smul 𝕜 (E → F) :=
    uniform_convergence_on.has_continuous_smul_of_image_bounded h𝔖₁,

end

end general

section bounded_sets

variables {𝕜 E F : Type*} [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
  [add_comm_group F] [module 𝕜 F] [topological_space E] [has_continuous_smul 𝕜 E]

instance [topological_space F] [topological_add_group F] : topological_space (E →L[𝕜] F) :=
strong_topology 𝕜 E F {S | bornology.is_vonN_bounded 𝕜 S}

instance [topological_space F] [topological_add_group F] : topological_add_group (E →L[𝕜] F) :=
strong_topology.topological_add_group 𝕜 E F _

instance [uniform_space F] [uniform_add_group F] : uniform_space (E →L[𝕜] F) :=
strong_uniformity 𝕜 E F {S | bornology.is_vonN_bounded 𝕜 S}

instance [uniform_space F] [uniform_add_group F] : uniform_add_group (E →L[𝕜] F) :=
strong_uniformity.uniform_add_group 𝕜 E F _

end bounded_sets

end continuous_linear_map
