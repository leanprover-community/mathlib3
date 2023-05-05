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

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains algebraic compatibility results about the uniform structure of uniform
convergence / `𝔖`-convergence. They will mostly be useful for defining strong topologies on the
space of continuous linear maps between two topological vector spaces.

## Main statements

* `uniform_fun.uniform_group` : if `G` is a uniform group, then `α →ᵤ G` a uniform group
* `uniform_on_fun.uniform_group` : if `G` is a uniform group, then for any `𝔖 : set (set α)`,
  `α →ᵤ[𝔖] G` a uniform group.
* `uniform_on_fun.has_continuous_smul_of_image_bounded` : let `E` be a TVS, `𝔖 : set (set α)` and
  `H` a submodule of `α →ᵤ[𝔖] E`. If the image of any `S ∈ 𝔖` by any `u ∈ H` is bounded (in the
  sense of `bornology.is_vonN_bounded`), then `H`, equipped with the topology induced from
  `α →ᵤ[𝔖] E`, is a TVS.

## Implementation notes

Like in `topology/uniform_space/uniform_convergence_topology`, we use the type aliases
`uniform_fun` (denoted `α →ᵤ β`) and `uniform_on_fun` (denoted `α →ᵤ[𝔖] β`) for functions from `α`
to `β` endowed with the structures of uniform convergence and `𝔖`-convergence.

## TODO

* `uniform_on_fun.has_continuous_smul_of_image_bounded` unnecessarily asks for `𝔖` to be
  nonempty and directed. This will be easy to solve once we know that replacing `𝔖` by its
  ***noncovering*** bornology (i.e ***not*** what `bornology` currently refers to in mathlib)
  doesn't change the topology.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, strong dual

-/

open filter
open_locale topology pointwise uniform_convergence

section algebraic_instances

variables {α β ι R : Type*} {𝔖 : set $ set α}

@[to_additive] instance [monoid β] : monoid (α →ᵤ β) := pi.monoid
@[to_additive] instance [monoid β] : monoid (α →ᵤ[𝔖] β) := pi.monoid

@[to_additive] instance [comm_monoid β] : comm_monoid (α →ᵤ β) := pi.comm_monoid
@[to_additive] instance [comm_monoid β] : comm_monoid (α →ᵤ[𝔖] β) := pi.comm_monoid

@[to_additive] instance [group β] : group (α →ᵤ β) := pi.group
@[to_additive] instance [group β] : group (α →ᵤ[𝔖] β) := pi.group

@[to_additive] instance [comm_group β] : comm_group (α →ᵤ β) := pi.comm_group
@[to_additive] instance [comm_group β] : comm_group (α →ᵤ[𝔖] β) := pi.comm_group

instance [semiring R] [add_comm_monoid β] [module R β] : module R (α →ᵤ β) := pi.module _ _ _
instance [semiring R] [add_comm_monoid β] [module R β] : module R (α →ᵤ[𝔖] β) := pi.module _ _ _

end algebraic_instances

section group

variables {α G ι : Type*} [group G] {𝔖 : set $ set α} [uniform_space G] [uniform_group G]

/-- If `G` is a uniform group, then `α →ᵤ G` is a uniform group as well. -/
@[to_additive "If `G` is a uniform additive group, then `α →ᵤ G` is a uniform additive group
as well."]
instance : uniform_group (α →ᵤ G) :=
-- Since `(/) : G × G → G` is uniformly continuous,
-- `uniform_fun.postcomp_uniform_continuous` tells us that
-- `((/) ∘ —) : (α →ᵤ G × G) → (α →ᵤ G)` is uniformly continuous too. By precomposing with
-- `uniform_fun.uniform_equiv_prod_arrow`, this gives that
-- `(/) : (α →ᵤ G) × (α →ᵤ G) → (α →ᵤ G)` is also uniformly continuous
⟨(uniform_fun.postcomp_uniform_continuous uniform_continuous_div).comp
  uniform_fun.uniform_equiv_prod_arrow.symm.uniform_continuous⟩

@[to_additive]
protected lemma uniform_fun.has_basis_nhds_one_of_basis {p : ι → Prop}
  {b : ι → set G} (h : (𝓝 1 : filter G).has_basis p b) :
  (𝓝 1 : filter (α →ᵤ G)).has_basis p
    (λ i, {f : α →ᵤ G | ∀ x, f x ∈ b i}) :=
begin
  have := h.comap (λ p : G × G, p.2 / p.1),
  rw ← uniformity_eq_comap_nhds_one at this,
  convert uniform_fun.has_basis_nhds_of_basis α _ 1 this,
  ext i f,
  simp [uniform_fun.gen]
end

@[to_additive]
protected lemma uniform_fun.has_basis_nhds_one :
  (𝓝 1 : filter (α →ᵤ G)).has_basis
    (λ V : set G, V ∈ (𝓝 1 : filter G))
    (λ V, {f : α → G | ∀ x, f x ∈ V}) :=
uniform_fun.has_basis_nhds_one_of_basis (basis_sets _)

/-- Let `𝔖 : set (set α)`. If `G` is a uniform group, then `α →ᵤ[𝔖] G` is a uniform group as
well. -/
@[to_additive "Let `𝔖 : set (set α)`. If `G` is a uniform additive group, then `α →ᵤ[𝔖] G` is a
uniform additive group as well. "]
instance : uniform_group (α →ᵤ[𝔖] G) :=
-- Since `(/) : G × G → G` is uniformly continuous,
-- `uniform_on_fun.postcomp_uniform_continuous` tells us that
-- `((/) ∘ —) : (α →ᵤ[𝔖] G × G) → (α →ᵤ[𝔖] G)` is uniformly continuous too. By precomposing with
-- `uniform_on_fun.uniform_equiv_prod_arrow`, this gives that
-- `(/) : (α →ᵤ[𝔖] G) × (α →ᵤ[𝔖] G) → (α →ᵤ[𝔖] G)` is also uniformly continuous
⟨(uniform_on_fun.postcomp_uniform_continuous uniform_continuous_div).comp
  uniform_on_fun.uniform_equiv_prod_arrow.symm.uniform_continuous⟩

@[to_additive]
protected lemma uniform_on_fun.has_basis_nhds_one_of_basis (𝔖 : set $ set α)
  (h𝔖₁ : 𝔖.nonempty) (h𝔖₂ : directed_on (⊆) 𝔖) {p : ι → Prop}
  {b : ι → set G} (h : (𝓝 1 : filter G).has_basis p b) :
  (𝓝 1 : filter (α →ᵤ[𝔖] G)).has_basis
    (λ Si : set α × ι, Si.1 ∈ 𝔖 ∧ p Si.2)
    (λ Si, {f : α →ᵤ[𝔖] G | ∀ x ∈ Si.1, f x ∈ b Si.2}) :=
begin
  have := h.comap (λ p : G × G, p.1 / p.2),
  rw ← uniformity_eq_comap_nhds_one_swapped at this,
  convert uniform_on_fun.has_basis_nhds_of_basis α _ 𝔖 1 h𝔖₁ h𝔖₂ this,
  ext i f,
  simp [uniform_on_fun.gen]
end

@[to_additive]
protected lemma uniform_on_fun.has_basis_nhds_one (𝔖 : set $ set α)
  (h𝔖₁ : 𝔖.nonempty) (h𝔖₂ : directed_on (⊆) 𝔖) :
  (𝓝 1 : filter (α →ᵤ[𝔖] G)).has_basis
    (λ SV : set α × set G, SV.1 ∈ 𝔖 ∧ SV.2 ∈ (𝓝 1 : filter G))
    (λ SV, {f : α →ᵤ[𝔖] G | ∀ x ∈ SV.1, f x ∈ SV.2}) :=
uniform_on_fun.has_basis_nhds_one_of_basis 𝔖 h𝔖₁ h𝔖₂ (basis_sets _)

end group

section module

variables (𝕜 α E H : Type*) {hom : Type*} [normed_field 𝕜] [add_comm_group H] [module 𝕜 H]
  [add_comm_group E] [module 𝕜 E] [topological_space H] [uniform_space E] [uniform_add_group E]
  [has_continuous_smul 𝕜 E] {𝔖 : set $ set α} [linear_map_class hom 𝕜 H (α →ᵤ[𝔖] E)]

/-- Let `E` be a TVS, `𝔖 : set (set α)` and `H` a submodule of `α →ᵤ[𝔖] E`. If the image of any
`S ∈ 𝔖` by any `u ∈ H` is bounded (in the sense of `bornology.is_vonN_bounded`), then `H`,
equipped with the topology of `𝔖`-convergence, is a TVS.

For convenience, we don't literally ask for `H : submodule (α →ᵤ[𝔖] E)`. Instead, we prove the
result for any vector space `H` equipped with a linear inducing to `α →ᵤ[𝔖] E`, which is often
easier to use. We also state the `submodule` version as
`uniform_on_fun.has_continuous_smul_submodule_of_image_bounded`. -/
lemma uniform_on_fun.has_continuous_smul_induced_of_image_bounded
  (h𝔖₁ : 𝔖.nonempty) (h𝔖₂ : directed_on (⊆) 𝔖)
  (φ : hom) (hφ : inducing φ)
  (h : ∀ u : H, ∀ s ∈ 𝔖, bornology.is_vonN_bounded 𝕜 ((φ u : α → E) '' s)) :
  has_continuous_smul 𝕜 H :=
begin
  haveI : topological_add_group H,
  { rw hφ.induced,
    exact topological_add_group_induced φ },
  have : (𝓝 0 : filter H).has_basis _ _,
  { rw [hφ.induced, nhds_induced, map_zero],
    exact ((uniform_on_fun.has_basis_nhds_zero 𝔖 h𝔖₁ h𝔖₂).comap φ) },
  refine has_continuous_smul.of_basis_zero this _ _ _,
  { rintros ⟨S, V⟩ ⟨hS, hV⟩,
    have : tendsto (λ kx : (𝕜 × E), kx.1 • kx.2) (𝓝 (0, 0)) (𝓝 $ (0 : 𝕜) • 0) :=
      continuous_smul.tendsto (0 : 𝕜 × E),
    rw [zero_smul, nhds_prod_eq] at this,
    have := this hV,
    rw [mem_map, mem_prod_iff] at this,
    rcases this with ⟨U, hU, W, hW, hUW⟩,
    refine ⟨U, hU, ⟨S, W⟩, ⟨hS, hW⟩, _⟩,
    rw set.smul_subset_iff,
    intros a ha u hu x hx,
    rw smul_hom_class.map_smul,
    exact hUW (⟨ha, hu x hx⟩ : (a, φ u x) ∈ U ×ˢ W) },
  { rintros a ⟨S, V⟩ ⟨hS, hV⟩,
    have : tendsto (λ x : E, a • x) (𝓝 0) (𝓝 $ a • 0) := tendsto_id.const_smul a,
    rw [smul_zero] at this,
    refine ⟨⟨S, ((•) a) ⁻¹' V⟩, ⟨hS, this hV⟩, λ f hf x hx, _⟩,
    rw [smul_hom_class.map_smul],
    exact hf x hx },
  { rintros u ⟨S, V⟩ ⟨hS, hV⟩,
    rcases h u S hS hV with ⟨r, hrpos, hr⟩,
    rw metric.eventually_nhds_iff_ball,
    refine ⟨r⁻¹, inv_pos.mpr hrpos, λ a ha x hx, _⟩,
    by_cases ha0 : a = 0,
    { rw ha0,
      simp [mem_of_mem_nhds hV] },
    { rw mem_ball_zero_iff at ha,
      rw [smul_hom_class.map_smul, pi.smul_apply],
      have : φ u x ∈ a⁻¹ • V,
      { have ha0 : 0<‖a‖ := norm_pos_iff.mpr ha0,
        refine (hr a⁻¹ _) (set.mem_image_of_mem (φ u) hx),
        rw [norm_inv, le_inv hrpos ha0],
        exact ha.le },
      rwa set.mem_inv_smul_set_iff₀ ha0 at this } }
end

/-- Let `E` be a TVS, `𝔖 : set (set α)` and `H` a submodule of `α →ᵤ[𝔖] E`. If the image of any
`S ∈ 𝔖` by any `u ∈ H` is bounded (in the sense of `bornology.is_vonN_bounded`), then `H`,
equipped with the topology of `𝔖`-convergence, is a TVS.

If you have a hard time using this lemma, try the one above instead. -/
lemma uniform_on_fun.has_continuous_smul_submodule_of_image_bounded
  (h𝔖₁ : 𝔖.nonempty) (h𝔖₂ : directed_on (⊆) 𝔖) (H : submodule 𝕜 (α →ᵤ[𝔖] E))
  (h : ∀ u ∈ H, ∀ s ∈ 𝔖, bornology.is_vonN_bounded 𝕜 (u '' s)) :
  @has_continuous_smul 𝕜 H _ _
  ((uniform_on_fun.topological_space α E 𝔖).induced (coe : H → α →ᵤ[𝔖] E)) :=
begin
  haveI : topological_add_group H := topological_add_group_induced
    (linear_map.id.dom_restrict H : H →ₗ[𝕜] α → E),
  exact uniform_on_fun.has_continuous_smul_induced_of_image_bounded 𝕜 α E H h𝔖₁ h𝔖₂
    (linear_map.id.dom_restrict H : H →ₗ[𝕜] α → E) inducing_coe (λ ⟨u, hu⟩, h u hu)
end

end module
