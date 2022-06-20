/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.uniform_space.uniform_convergence_topology
import analysis.locally_convex.bounded
import topology.algebra.filter_basis

/-!
# Algebraic facts about the topology of uniform convergence

This file contaains algrebraic compatibility results about the uniform structure of uniform
convergence / `𝔖`-convergence. They will mostly be useful for defining strong topologies on the
space of continuous linear maps between two topological vector spaces.

## Main statements

* `uniform_convergence.uniform_group` : if `G` is a uniform group, then the uniform structure of
  uniform convergence makes `α → G` an uniform group
* `uniform_convergence_on.uniform_group` : if `G` is a uniform group, then the uniform structure of
  `𝔖`-convergence, for any `𝔖 : set (set α)`, makes `α → G` an uniform group

## TODO

* Let `E` be a TVS, `𝔖 : set (set α)` and `H` a submodule of `α → E`. If the image of any `S ∈ 𝔖`
  by any `u ∈ H` is bounded (in the sense of `bornology.is_vonN_bounded`), then `H`, equipped with
  the topology of `𝔖`-convergence, is a TVS.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]

## Tags

uniform convergence, strong dual

-/

open filter
open_locale topological_space

section group

variables {α G : Type*} [group G] [uniform_space G] [uniform_group G] {𝔖 : set $ set α}

local attribute [-instance] Pi.uniform_space
local attribute [-instance] Pi.topological_space
local attribute [instance] uniform_convergence.uniform_space

@[to_additive]
protected lemma uniform_convergence.uniform_group :
  uniform_group (α → G) :=
⟨(uniform_convergence.postcomp_uniform_continuous uniform_continuous_div).comp
  uniform_convergence.uniform_equiv_prod_arrow.symm.uniform_continuous⟩

@[to_additive]
protected lemma uniform_convergence.has_basis_nhds_one_of_basis {ι : Type*} {p : ι → Prop}
  {s : ι → set G} (h : (𝓝 1 : filter G).has_basis p s) :
  (𝓝 1 : filter (α → G)).has_basis p (λ i, {f : α → G | ∀ x, f x ∈ s i}) :=
begin
  --refine uniform_convergence.has_basis_nhds_of_basis
end

local attribute [-instance] uniform_convergence.uniform_space

@[to_additive]
protected lemma uniform_convergence_on.uniform_group :
  @uniform_group (α → G) (uniform_convergence_on.uniform_space α G 𝔖) _ :=
begin
  letI : uniform_space (α → G) := uniform_convergence_on.uniform_space α G 𝔖,
  letI : uniform_space (α → G × G) := uniform_convergence_on.uniform_space α (G × G) 𝔖,
  exact ⟨(uniform_convergence_on.postcomp_uniform_continuous uniform_continuous_div).comp
          uniform_convergence_on.uniform_equiv_prod_arrow.symm.uniform_continuous⟩
end

end group

section module

variables {α 𝕜 E : Type*} [semi_normed_comm_ring 𝕜] [add_comm_group E] [module 𝕜 E]
  [uniform_space E] [uniform_add_group E] [has_continuous_smul 𝕜 E] {𝔖 : set $ set α}
  (h𝔖₁ : 𝔖.nonempty) (h𝔖₂ : directed_on (⊆) 𝔖) (H : submodule 𝕜 (α → E))

local attribute [-instance] Pi.uniform_space
local attribute [-instance] Pi.topological_space

include h𝔖₁ h𝔖₂

lemma goal (h : ∀ u ∈ H, ∀ s ∈ 𝔖, bornology.is_vonN_bounded 𝕜 (u '' s)) :
  @has_continuous_smul 𝕜 H _ _
  ((uniform_convergence_on.topological_space α E 𝔖).induced (coe : H → α → E)) :=
begin
  letI : uniform_space (α → E) := uniform_convergence_on.uniform_space α E 𝔖,
  haveI : uniform_add_group (α → E) := uniform_convergence_on.uniform_add_group,
  haveI : topological_add_group H := topological_add_group_induced
    (linear_map.id.dom_restrict H : H →ₗ[𝕜] α → E),
  have : (𝓝 0 : filter H).has_basis _ _,
  { rw [nhds_induced, submodule.coe_zero],
    exact ((uniform_convergence_on.has_basis_nhds α E 𝔖 0 h𝔖₁ h𝔖₂).comap (coe : H → α → E)) },
  refine has_continuous_smul.of_basis_zero this _ _ _,
  { have : tendsto (λ kx : (𝕜 × E), kx.1 • kx.2) (𝓝 0) (𝓝 $ (0 : 𝕜) • 0) :=
      continuous_smul.tendsto (0 : 𝕜 × E),
    rw zero_smul at this,
    rintros ⟨S, V⟩ ⟨hS, hV⟩,  },
  sorry,
  { rintros ⟨u, hu⟩ ⟨S, V⟩ ⟨hS, hV⟩,
    let V' := {e : E | (e, (0 : E)) ∈ V},
    have hV' : V' ∈ (𝓝 0 : filter E) := mem_nhds_right 0 hV,
    rcases h u hu S hS hV' with ⟨r, hrpos, hr⟩,
    rw metric.eventually_nhds_iff_ball,
    refine ⟨r⁻¹, inv_pos.mpr hrpos, λ a ha x hx, _⟩,
    rw mem_ball_zero_iff at ha,
    sorry }
end

end module
