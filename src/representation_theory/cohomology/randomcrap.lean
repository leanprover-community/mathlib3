import representation_theory.cohomology.profiniteummmmmmmm

open topological_space ProfiniteGroup
#check nhds
def locally_profinite (G : Type*) [group G] [topological_space G] : Prop :=
∀ U : opens G, (1 : G) ∈ U → ∃ V : open_subgroup G, (V : set G) ⊆ U ∧ is_compact (V : set G)

lemma locally_profinite_mul {G : Type*} [group G] [topological_space G] [has_continuous_mul G]
  (h : locally_profinite G) (U : opens G) (g : G) (hg : g ∈ U) :
  ∃ V : open_subgroup G, (left_coset g (V : set G)) ⊆ U ∧ is_compact (V : set G) :=
begin
  have : (1 : G) ∈ left_coset g⁻¹ U := ⟨g, hg, inv_mul_self _⟩,
  rcases h ⟨left_coset g⁻¹ U, is_open.left_coset U.2 _⟩ this with ⟨V, hV, hVc⟩,
  use V,
  split,
  rintros x ⟨y, hy, rfl⟩,
  rcases hV hy with ⟨w, hw, rfl⟩,
  dsimp at *,
  rw mul_inv_cancel_left,
  exact hw,
  assumption,
end

lemma is_open_iff_is_clopen {G : Type*} [group G] [topological_space G] [has_continuous_mul G]
  (U : subgroup G) :
  is_open (U : set G) ↔ is_clopen (U : set G) :=
⟨λ hU, ⟨hU, open_subgroup.is_closed ⟨U, hU⟩⟩, λ hU, hU.1⟩
#check mem_nhds_iff

lemma is_compact.left_coset {G : Type*} [group G] [topological_space G] [has_continuous_mul G]
  (U : set G) (h : is_compact U) (g : G) :
  is_compact (left_coset g U) :=
is_compact.image h (continuous_mul_left _)
#check totally_disconnected_space
lemma locally_compact_of_locally_profinite {G : Type*} [group G] [topological_space G]
  [has_continuous_mul G] (h : locally_profinite G) : locally_compact_space G :=
begin
  constructor,
  intros g S hS,
  rcases mem_nhds_iff.1 hS with ⟨U, hU, hUS⟩,
  rcases locally_profinite_mul h ⟨U, hUS.1⟩ g hUS.2 with ⟨V, hV, hVc⟩,
  use left_coset g V,
  split,
  exact is_open.mem_nhds (is_open.left_coset V.2 _) ⟨1, V.1.one_mem, mul_one _⟩,
  split,
  exact subset_trans hV hU,
  exact is_compact.left_coset _ hVc _ ,
end
#check open_subgroup.is_closed
lemma locally_profinite_of_ProfiniteGroup (G : ProfiniteGroup) :
  locally_profinite G :=
begin
  sorry,
end
