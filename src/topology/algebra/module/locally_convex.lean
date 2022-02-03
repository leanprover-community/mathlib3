/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.convex.topology
import analysis.normed_space.basic
/-! TODO -/

open topological_space filter

open_locale topological_space

section semimodule

class locally_convex_space (𝕂 E : Type*) [ordered_semiring 𝕂] [add_comm_monoid E] [module 𝕂 E]
  [topological_space E] : Prop :=
(convex_basis : ∀ x : E, (𝓝 x).has_basis (λ (s : set E), s ∈ 𝓝 x ∧ convex 𝕂 s) id)

variables (𝕂 E : Type*) [ordered_semiring 𝕂] [add_comm_monoid E] [module 𝕂 E]
  [topological_space 𝕂] [topological_space E] [topological_ring 𝕂] [has_continuous_add E]
  [has_continuous_smul 𝕂 E]

lemma locally_convex_of_bases {ι : Type*} (b : E → ι → set E) (p : ι → Prop)
  (hbasis : ∀ x : E, (𝓝 x).has_basis p (b x)) (hconvex : ∀ x i, p i → convex 𝕂 (b x i)) :
  locally_convex_space 𝕂 E :=
⟨λ x, (hbasis x).to_has_basis
  (λ i hi, ⟨b x i, ⟨⟨(hbasis x).mem_of_mem hi, hconvex x i hi⟩, le_refl (b x i)⟩⟩)
  (λ s hs, ⟨(hbasis x).index s hs.1,
    ⟨(hbasis x).property_index hs.1, (hbasis x).set_index_subset hs.1⟩⟩)⟩

lemma locally_convex_space.convex_basis_zero [locally_convex_space 𝕂 E] :
  (𝓝 0 : filter E).has_basis (λ s, s ∈ (𝓝 0 : filter E) ∧ convex 𝕂 s) id :=
locally_convex_space.convex_basis 0

lemma locally_convex_iff_exists_convex_subset :
  locally_convex_space 𝕂 E ↔ ∀ x : E, ∀ U ∈ 𝓝 x, ∃ S ∈ 𝓝 x, convex 𝕂 S ∧ S ⊆ U :=
begin
  split,
  { intros h x U hU,
    convert (has_basis_iff.mp (@locally_convex_space.convex_basis 𝕂 E _ _ _ _ h x) U).mp hU,
    ext S,
    tauto },

end

end semimodule

section module

variables (𝕂 E : Type*) [ordered_semiring 𝕂] [add_comm_group E] [module 𝕂 E]
  [topological_space 𝕂] [topological_space E] [topological_ring 𝕂] [topological_add_group E]
  [has_continuous_smul 𝕂 E]

lemma locally_convex_of_basis_zero {ι : Type*} (b : ι → set E) (p : ι → Prop)
  (hbasis : (𝓝 0).has_basis p b) (hconvex : ∀ i, p i → convex 𝕂 (b i)) :
  locally_convex_space 𝕂 E :=
begin
  refine locally_convex_of_bases 𝕂 E (λ (x : E) (i : ι), ((+) x) '' b i) p (λ x, _)
    (λ x i hi, (hconvex i hi).translate x),
  rw ← map_add_left_nhds_zero,
  exact hbasis.map _
end

end module

namespace normed_space

variables {E : Type*} [normed_group E] [normed_space ℝ E]

instance : locally_convex_space ℝ E :=
locally_convex_of_basis_zero ℝ E (metric.ball 0) (λ (ε : ℝ), 0 < ε) metric.nhds_basis_ball
  (λ ε hε, convex_ball (0 : E) ε)

end normed_space
