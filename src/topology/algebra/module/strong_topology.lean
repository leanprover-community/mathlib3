/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.algebra.uniform_convergence

/-!
# Strong topologies on the space of continuous linear maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define the strong topologies on `E →L[𝕜] F` associated with a family
`𝔖 : set (set E)` to be the topology of uniform convergence on the elements of `𝔖` (also called
the topology of `𝔖`-convergence).

The lemma `uniform_on_fun.has_continuous_smul_of_image_bounded` tells us that this is a
vector space topology if the continuous linear image of any element of `𝔖` is bounded (in the sense
of `bornology.is_vonN_bounded`).

We then declare an instance for the case where `𝔖` is exactly the set of all bounded subsets of
`E`, giving us the so-called "topology of uniform convergence on bounded sets" (or "topology of
bounded convergence"), which coincides with the operator norm topology in the case of
`normed_space`s.

Other useful examples include the weak-* topology (when `𝔖` is the set of finite sets or the set
of singletons) and the topology of compact convergence (when `𝔖` is the set of relatively compact
sets).

## Main definitions

* `continuous_linear_map.strong_topology` is the topology mentioned above for an arbitrary `𝔖`.
* `continuous_linear_map.topological_space` is the topology of bounded convergence. This is
  declared as an instance.

## Main statements

* `continuous_linear_map.strong_topology.topological_add_group` and
  `continuous_linear_map.strong_topology.has_continuous_smul` show that the strong topology
  makes `E →L[𝕜] F` a topological vector space, with the assumptions on `𝔖` mentioned above.
* `continuous_linear_map.topological_add_group` and
  `continuous_linear_map.has_continuous_smul` register these facts as instances for the special
  case of bounded convergence.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## TODO

* add a type alias for continuous linear maps with the topology of `𝔖`-convergence?

## Tags

uniform convergence, bounded convergence
-/

open_locale topology uniform_convergence

namespace continuous_linear_map

section general

variables {𝕜₁ 𝕜₂ : Type*} [normed_field 𝕜₁] [normed_field 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂)
  {E E' F F' : Type*} [add_comm_group E] [module 𝕜₁ E] [add_comm_group E'] [module ℝ E']
  [add_comm_group F] [module 𝕜₂ F] [add_comm_group F'] [module ℝ F']
  [topological_space E] [topological_space E'] (F)

/-- Given `E` and `F` two topological vector spaces and `𝔖 : set (set E)`, then
`strong_topology σ F 𝔖` is the "topology of uniform convergence on the elements of `𝔖`" on
`E →L[𝕜] F`.

If the continuous linear image of any element of `𝔖` is bounded, this makes `E →L[𝕜] F` a
topological vector space. -/
def strong_topology [topological_space F] [topological_add_group F]
  (𝔖 : set (set E)) : topological_space (E →SL[σ] F) :=
(@uniform_on_fun.topological_space E F
  (topological_add_group.to_uniform_space F) 𝔖).induced coe_fn

/-- The uniform structure associated with `continuous_linear_map.strong_topology`. We make sure
that this has nice definitional properties. -/
def strong_uniformity [uniform_space F] [uniform_add_group F]
  (𝔖 : set (set E)) : uniform_space (E →SL[σ] F) :=
@uniform_space.replace_topology _ (strong_topology σ F 𝔖)
  ((uniform_on_fun.uniform_space E F 𝔖).comap coe_fn)
  (by rw [strong_topology, uniform_add_group.to_uniform_space_eq]; refl)

@[simp] lemma strong_uniformity_topology_eq [uniform_space F] [uniform_add_group F]
  (𝔖 : set (set E)) :
  (strong_uniformity σ F 𝔖).to_topological_space = strong_topology σ F 𝔖 :=
rfl

lemma strong_uniformity.uniform_embedding_coe_fn [uniform_space F] [uniform_add_group F]
  (𝔖 : set (set E)) :
  @uniform_embedding (E →SL[σ] F) (E →ᵤ[𝔖] F) (strong_uniformity σ F 𝔖)
  (uniform_on_fun.uniform_space E F 𝔖) coe_fn :=
begin
  letI : uniform_space (E →SL[σ] F) := strong_uniformity σ F 𝔖,
  exact ⟨⟨rfl⟩, fun_like.coe_injective⟩
end

lemma strong_topology.embedding_coe_fn [uniform_space F] [uniform_add_group F]
  (𝔖 : set (set E)) :
  @embedding (E →SL[σ] F) (E →ᵤ[𝔖] F) (strong_topology σ F 𝔖)
  (uniform_on_fun.topological_space E F 𝔖)
  (uniform_on_fun.of_fun 𝔖 ∘ coe_fn) :=
@uniform_embedding.embedding _ _ (_root_.id _) _ _
  (strong_uniformity.uniform_embedding_coe_fn _ _ _)

lemma strong_uniformity.uniform_add_group [uniform_space F] [uniform_add_group F]
  (𝔖 : set (set E)) : @uniform_add_group (E →SL[σ] F) (strong_uniformity σ F 𝔖) _ :=
begin
  letI : uniform_space (E →SL[σ] F) := strong_uniformity σ F 𝔖,
  rw [strong_uniformity, uniform_space.replace_topology_eq],
  let φ : (E →SL[σ] F) →+ E →ᵤ[𝔖] F := ⟨(coe_fn : (E →SL[σ] F) → E →ᵤ F), rfl, λ _ _, rfl⟩,
  exact uniform_add_group_comap φ
end

lemma strong_topology.topological_add_group [topological_space F] [topological_add_group F]
  (𝔖 : set (set E)) : @topological_add_group (E →SL[σ] F) (strong_topology σ F 𝔖) _ :=
begin
  letI : uniform_space F := topological_add_group.to_uniform_space F,
  haveI : uniform_add_group F := topological_add_comm_group_is_uniform,
  letI : uniform_space (E →SL[σ] F) := strong_uniformity σ F 𝔖,
  haveI : uniform_add_group (E →SL[σ] F) := strong_uniformity.uniform_add_group σ F 𝔖,
  apply_instance
end

lemma strong_topology.t2_space [topological_space F] [topological_add_group F] [t2_space F]
  (𝔖 : set (set E)) (h𝔖 : ⋃₀ 𝔖 = set.univ) : @t2_space (E →SL[σ] F) (strong_topology σ F 𝔖) :=
begin
  letI : uniform_space F := topological_add_group.to_uniform_space F,
  haveI : uniform_add_group F := topological_add_comm_group_is_uniform,
  letI : topological_space (E →SL[σ] F) := strong_topology σ F 𝔖,
  haveI : t2_space (E →ᵤ[𝔖] F) := uniform_on_fun.t2_space_of_covering h𝔖,
  exact (strong_topology.embedding_coe_fn σ F 𝔖).t2_space
end

lemma strong_topology.has_continuous_smul [ring_hom_surjective σ] [ring_hom_isometric σ]
  [topological_space F] [topological_add_group F] [has_continuous_smul 𝕜₂ F] (𝔖 : set (set E))
  (h𝔖₁ : 𝔖.nonempty) (h𝔖₂ : directed_on (⊆) 𝔖) (h𝔖₃ : ∀ S ∈ 𝔖, bornology.is_vonN_bounded 𝕜₁ S) :
  @has_continuous_smul 𝕜₂ (E →SL[σ] F) _ _ (strong_topology σ F 𝔖) :=
begin
  letI : uniform_space F := topological_add_group.to_uniform_space F,
  haveI : uniform_add_group F := topological_add_comm_group_is_uniform,
  letI : topological_space (E →SL[σ] F) := strong_topology σ F 𝔖,
  let φ : (E →SL[σ] F) →ₗ[𝕜₂] E →ᵤ[𝔖] F :=
    ⟨(coe_fn : (E →SL[σ] F) → E → F), λ _ _, rfl, λ _ _, rfl⟩,
  exact uniform_on_fun.has_continuous_smul_induced_of_image_bounded 𝕜₂ E F (E →SL[σ] F)
    h𝔖₁ h𝔖₂ φ ⟨rfl⟩ (λ u s hs, (h𝔖₃ s hs).image u)
end

lemma strong_topology.has_basis_nhds_zero_of_basis [topological_space F] [topological_add_group F]
  {ι : Type*} (𝔖 : set (set E)) (h𝔖₁ : 𝔖.nonempty) (h𝔖₂ : directed_on (⊆) 𝔖) {p : ι → Prop}
  {b : ι → set F} (h : (𝓝 0 : filter F).has_basis p b) :
  (@nhds (E →SL[σ] F) (strong_topology σ F 𝔖) 0).has_basis
    (λ Si : set E × ι, Si.1 ∈ 𝔖 ∧ p Si.2)
    (λ Si, {f : E →SL[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2}) :=
begin
  letI : uniform_space F := topological_add_group.to_uniform_space F,
  haveI : uniform_add_group F := topological_add_comm_group_is_uniform,
  rw nhds_induced,
  exact (uniform_on_fun.has_basis_nhds_zero_of_basis 𝔖 h𝔖₁ h𝔖₂ h).comap coe_fn
end

lemma strong_topology.has_basis_nhds_zero [topological_space F] [topological_add_group F]
  (𝔖 : set (set E)) (h𝔖₁ : 𝔖.nonempty) (h𝔖₂ : directed_on (⊆) 𝔖) :
  (@nhds (E →SL[σ] F) (strong_topology σ F 𝔖) 0).has_basis
    (λ SV : set E × set F, SV.1 ∈ 𝔖 ∧ SV.2 ∈ (𝓝 0 : filter F))
    (λ SV, {f : E →SL[σ] F | ∀ x ∈ SV.1, f x ∈ SV.2}) :=
strong_topology.has_basis_nhds_zero_of_basis σ F 𝔖 h𝔖₁ h𝔖₂ (𝓝 0).basis_sets

end general

section bounded_sets

variables {𝕜₁ 𝕜₂ 𝕜₃ : Type*} [normed_field 𝕜₁] [normed_field 𝕜₂] [normed_field 𝕜₃]
  {σ : 𝕜₁ →+* 𝕜₂} {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [ring_hom_comp_triple σ τ ρ]
  {E E' F F' G : Type*}
  [add_comm_group E] [module 𝕜₁ E] [add_comm_group E'] [module ℝ E']
  [add_comm_group F] [module 𝕜₂ F] [add_comm_group F'] [module ℝ F']
  [add_comm_group G] [module 𝕜₃ G]
  [topological_space E]

/-- The topology of bounded convergence on `E →L[𝕜] F`. This coincides with the topology induced by
the operator norm when `E` and `F` are normed spaces. -/
instance [topological_space F] [topological_add_group F] : topological_space (E →SL[σ] F) :=
strong_topology σ F {S | bornology.is_vonN_bounded 𝕜₁ S}

instance [topological_space F] [topological_add_group F] : topological_add_group (E →SL[σ] F) :=
strong_topology.topological_add_group σ F _

instance [ring_hom_surjective σ] [ring_hom_isometric σ] [topological_space F]
  [topological_add_group F] [has_continuous_smul 𝕜₂ F] :
  has_continuous_smul 𝕜₂ (E →SL[σ] F) :=
strong_topology.has_continuous_smul σ F {S | bornology.is_vonN_bounded 𝕜₁ S}
  ⟨∅, bornology.is_vonN_bounded_empty 𝕜₁ E⟩
  (directed_on_of_sup_mem $ λ _ _, bornology.is_vonN_bounded.union)
  (λ s hs, hs)

instance [uniform_space F] [uniform_add_group F] : uniform_space (E →SL[σ] F) :=
strong_uniformity σ F {S | bornology.is_vonN_bounded 𝕜₁ S}

instance [uniform_space F] [uniform_add_group F] : uniform_add_group (E →SL[σ] F) :=
strong_uniformity.uniform_add_group σ F _

instance [topological_space F] [topological_add_group F] [has_continuous_smul 𝕜₁ E] [t2_space F] :
  t2_space (E →SL[σ] F) :=
strong_topology.t2_space σ F _ (set.eq_univ_of_forall $ λ x,
  set.mem_sUnion_of_mem (set.mem_singleton x) (bornology.is_vonN_bounded_singleton x))

protected lemma has_basis_nhds_zero_of_basis [topological_space F]
  [topological_add_group F] {ι : Type*} {p : ι → Prop} {b : ι → set F}
  (h : (𝓝 0 : filter F).has_basis p b) :
  (𝓝 (0 : E →SL[σ] F)).has_basis
    (λ Si : set E × ι, bornology.is_vonN_bounded 𝕜₁ Si.1 ∧ p Si.2)
    (λ Si, {f : E →SL[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2}) :=
strong_topology.has_basis_nhds_zero_of_basis σ F
  {S | bornology.is_vonN_bounded 𝕜₁ S} ⟨∅, bornology.is_vonN_bounded_empty 𝕜₁ E⟩
  (directed_on_of_sup_mem $ λ _ _, bornology.is_vonN_bounded.union) h

protected lemma has_basis_nhds_zero [topological_space F]
  [topological_add_group F] :
  (𝓝 (0 : E →SL[σ] F)).has_basis
    (λ SV : set E × set F, bornology.is_vonN_bounded 𝕜₁ SV.1 ∧ SV.2 ∈ (𝓝 0 : filter F))
    (λ SV, {f : E →SL[σ] F | ∀ x ∈ SV.1, f x ∈ SV.2}) :=
continuous_linear_map.has_basis_nhds_zero_of_basis (𝓝 0).basis_sets

variables (G) [topological_space F] [topological_space G]

/-- Pre-composition by a *fixed* continuous linear map as a continuous linear map.
Note that in non-normed space it is not always true that composition is continuous
in both variables, so we have to fix one of them. -/
@[simps] def precomp [topological_add_group G] [has_continuous_const_smul 𝕜₃ G]
  [ring_hom_surjective σ] [ring_hom_isometric σ] (L : E →SL[σ] F) :
  (F →SL[τ] G) →L[𝕜₃] (E →SL[ρ] G) :=
{ to_fun := λ f, f.comp L,
  map_add' := λ f g, add_comp f g L,
  map_smul' := λ a f, smul_comp a f L,
  cont :=
  begin
    letI : uniform_space G := topological_add_group.to_uniform_space G,
    haveI : uniform_add_group G := topological_add_comm_group_is_uniform,
    rw (strong_topology.embedding_coe_fn _ _ _).continuous_iff,
    refine (uniform_on_fun.precomp_uniform_continuous _).continuous.comp
      (strong_topology.embedding_coe_fn _ _ _).continuous,
    exact λ S hS, hS.image L,
  end }

variables (E) {G}

/-- Post-composition by a *fixed* continuous linear map as a continuous linear map.
Note that in non-normed space it is not always true that composition is continuous
in both variables, so we have to fix one of them. -/
@[simps] def postcomp [topological_add_group F] [topological_add_group G]
  [has_continuous_const_smul 𝕜₃ G] [has_continuous_const_smul 𝕜₂ F] (L : F →SL[τ] G) :
  (E →SL[σ] F) →SL[τ] (E →SL[ρ] G) :=
{ to_fun := λ f, L.comp f,
  map_add' := comp_add L,
  map_smul' := comp_smulₛₗ L,
  cont :=
  begin
    letI : uniform_space G := topological_add_group.to_uniform_space G,
    haveI : uniform_add_group G := topological_add_comm_group_is_uniform,
    letI : uniform_space F := topological_add_group.to_uniform_space F,
    haveI : uniform_add_group F := topological_add_comm_group_is_uniform,
    rw (strong_topology.embedding_coe_fn _ _ _).continuous_iff,
    exact (uniform_on_fun.postcomp_uniform_continuous L.uniform_continuous).continuous.comp
      (strong_topology.embedding_coe_fn _ _ _).continuous
  end }

end bounded_sets

end continuous_linear_map

open continuous_linear_map

namespace continuous_linear_equiv

section semilinear

variables {𝕜 : Type*} {𝕜₂ : Type*} {𝕜₃ : Type*} {𝕜₄ : Type*}
  {E : Type*} {F : Type*} {G : Type*} {H : Type*}
  [add_comm_group E] [add_comm_group F] [add_comm_group G] [add_comm_group H]
  [nontrivially_normed_field 𝕜] [nontrivially_normed_field 𝕜₂] [nontrivially_normed_field 𝕜₃]
    [nontrivially_normed_field 𝕜₄]
  [module 𝕜 E] [module 𝕜₂ F] [module 𝕜₃ G] [module 𝕜₄ H]
  [topological_space E] [topological_space F] [topological_space G] [topological_space H]
  [topological_add_group G] [topological_add_group H]
  [has_continuous_const_smul 𝕜₃ G] [has_continuous_const_smul 𝕜₄ H]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃} {σ₃₄ : 𝕜₃ →+* 𝕜₄}
    {σ₄₃ : 𝕜₄ →+* 𝕜₃} {σ₂₄ : 𝕜₂ →+* 𝕜₄} {σ₁₄ : 𝕜 →+* 𝕜₄}
  [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂] [ring_hom_inv_pair σ₃₄ σ₄₃]
    [ring_hom_inv_pair σ₄₃ σ₃₄]
  [ring_hom_comp_triple σ₂₁ σ₁₄ σ₂₄] [ring_hom_comp_triple σ₂₄ σ₄₃ σ₂₃]
    [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] [ring_hom_comp_triple σ₁₃ σ₃₄ σ₁₄]
    [ring_hom_comp_triple σ₂₃ σ₃₄ σ₂₄] [ring_hom_comp_triple σ₁₂ σ₂₄ σ₁₄]
  [ring_hom_isometric σ₁₂] [ring_hom_isometric σ₂₁]

include σ₁₄ σ₂₄ σ₁₃ σ₃₄ σ₂₁ σ₂₃

/-- A pair of continuous (semi)linear equivalences generates a (semi)linear equivalence between the
spaces of continuous (semi)linear maps. -/
@[simps] def arrow_congrSL (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G) :
  (E →SL[σ₁₄] H) ≃SL[σ₄₃] (F →SL[σ₂₃] G) :=
{ -- given explicitly to help `simps`
  to_fun := λ L, (e₄₃ : H →SL[σ₄₃] G).comp (L.comp (e₁₂.symm : F →SL[σ₂₁] E)),
  -- given explicitly to help `simps`
  inv_fun := λ L, (e₄₃.symm : G →SL[σ₃₄] H).comp (L.comp (e₁₂ : E →SL[σ₁₂] F)),
  map_add' := λ f g, by rw [add_comp, comp_add],
  map_smul' := λ t f, by rw [smul_comp, comp_smulₛₗ],
  continuous_to_fun :=
    ((postcomp F e₄₃.to_continuous_linear_map).comp
      (precomp H e₁₂.symm.to_continuous_linear_map)).continuous,
  continuous_inv_fun :=
    ((precomp H e₁₂.to_continuous_linear_map).comp
      (postcomp F e₄₃.symm.to_continuous_linear_map)).continuous,
  .. e₁₂.arrow_congr_equiv e₄₃, }

end semilinear

section linear
variables {𝕜 : Type*} {E : Type*} {F : Type*} {G : Type*} {H : Type*}
  [add_comm_group E] [add_comm_group F] [add_comm_group G] [add_comm_group H]
  [nontrivially_normed_field 𝕜] [module 𝕜 E] [module 𝕜 F] [module 𝕜 G] [module 𝕜 H]
  [topological_space E] [topological_space F] [topological_space G] [topological_space H]
  [topological_add_group G] [topological_add_group H]
  [has_continuous_const_smul 𝕜 G] [has_continuous_const_smul 𝕜 H]

/-- A pair of continuous linear equivalences generates an continuous linear equivalence between
the spaces of continuous linear maps. -/
def arrow_congr (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) : (E →L[𝕜] H) ≃L[𝕜] (F →L[𝕜] G) :=
e₁.arrow_congrSL e₂

end linear

end continuous_linear_equiv
