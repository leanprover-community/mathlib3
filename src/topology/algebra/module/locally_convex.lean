import analysis.convex.topology
import analysis.normed_space.basic
/-! TODO -/

open topological_space filter

open_locale topological_space

section semimodule

class locally_convex_space (𝕂 E : Type*) [ordered_semiring 𝕂] [add_comm_monoid E] [module 𝕂 E]
  [topological_space 𝕂] [topological_space E] [topological_ring 𝕂] [has_continuous_add E]
  [has_continuous_smul 𝕂 E] :=
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

--⟨λ s hs, let ⟨i, h_pi, h_sub⟩ := hbasis.mem_iff.mp hs in
--  ⟨b i, hbasis.mem_of_mem h_pi, h_sub, hconvex i (h_pi)⟩⟩

--lemma locally_convex_space.exists_convex_nhds_zero [locally_convex_space 𝕂 E] {s : set E}
--  (hs : s ∈ (𝓝 0 : filter E)) : ∃ c ∈ (𝓝 0 : filter E), c ⊆ s ∧ convex 𝕂 c :=
--@locally_convex_space.exists_convex_nhds_zero' 𝕂 E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› s hs

--def locally_convex_space.nhds_zero_basis_convex [h : locally_convex_space 𝕂 E] :
--  (𝓝 0 : filter E).has_basis (λ c : set E, c ∈ (𝓝 0 : filter E) ∧ convex 𝕂 c) id :=
--⟨ λ t,
--  ⟨ λ ht,
--    let ⟨c, c_mem_nhds, c_sub_t, c_convex⟩ := locally_convex_space.exists_convex_nhds_zero 𝕂 E
--ht in
--    ⟨c, ⟨c_mem_nhds, c_convex⟩, c_sub_t⟩,
--    λ ⟨c, ⟨c_mem_nhds, _⟩, c_sub_t⟩, filter.mem_of_superset c_mem_nhds c_sub_t ⟩ ⟩

--def locally_convex_space.nhds_basis_convex [h : locally_convex_space 𝕂 E] (x : E) :
--  (𝓝 x).has_basis (λ c : set E, c ∈ (𝓝 x) ∧ convex 𝕂 c) id :=
--sorry

--lemma locally_convex_space_of_convex_nhds_basis {ι : Type*} {b : ι → set E} {p : ι → Prop}
--  (hbasis : (𝓝 0 : filter E).has_basis p b) (hconvex : ∀ i, p i → convex 𝕂 (b i)) :
--  locally_convex_space 𝕂 E :=
--⟨λ s hs, let ⟨i, h_pi, h_sub⟩ := hbasis.mem_iff.mp hs in
--  ⟨b i, hbasis.mem_of_mem h_pi, h_sub, hconvex i (h_pi)⟩⟩

end module

namespace normed_space

variables {E : Type*} [normed_group E] [normed_space ℝ E]

noncomputable instance : locally_convex_space ℝ E :=
locally_convex_of_basis_zero ℝ E (metric.ball 0) (λ (ε : ℝ), 0 < ε) metric.nhds_basis_ball
  (λ ε hε, convex_ball (0 : E) ε)

end normed_space

section lattice_ops

variables {ι 𝕂 E : Type*} [ordered_semiring 𝕂] [add_comm_monoid E] [module 𝕂 E]
  [topological_space 𝕂] [topological_ring 𝕂]
  {t : topological_space E} [@has_continuous_add E t _] [@has_continuous_smul 𝕂 E _ _ t]
  {ts : ι → topological_space E} [Π i, @has_continuous_add E (ts i) _]
  [Π i, @has_continuous_smul 𝕂 E _ _ (ts i)]

--instance locally_convex_infi : @locally_convex_space 𝕂 E _ _ _ _ (⨅ i, ts i) _ _ _ :=
--@locally_convex_space_of_convex_nhds_basis 𝕂  E _ _ _ _ (⨅ i, ts i) _ _ _ (set E)

end lattice_ops
