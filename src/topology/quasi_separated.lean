import topology.subset_properties

variables {α β : Type*} [topological_space α] [topological_space β] (f : α → β)

def is_quasi_separated (s : set α) : Prop :=
∀ (U V : set α), U ⊆ s → is_open U → is_compact U → V ⊆ s →
  is_open V → is_compact V → is_compact (U ∩ V)

@[mk_iff]
class quasi_separated_space (α : Type*) [topological_space α] : Prop :=
(inter_is_compact : ∀ (U V : set α),
  is_open U → is_compact U → is_open V → is_compact V → is_compact (U ∩ V))

lemma is_quasi_separated_univ (α : Type*) [topological_space α] :
  is_quasi_separated (set.univ : set α) ↔ quasi_separated_space α :=
begin
  rw quasi_separated_space_iff,
  simp [is_quasi_separated],
end

lemma open_embedding.is_quasi_separated_iff {f : α → β} (h : open_embedding f) (s : set α) :
  is_quasi_separated s ↔ is_quasi_separated (f '' s) :=
begin
  split,
  { intros H U V hU hU' hU'' hV hV' hV'',
    convert (H (f ⁻¹' U) (f ⁻¹' V) _ (h.continuous.1 _ hU') _ _ (h.continuous.1 _ hV') _).image
      h.continuous,
    { symmetry,
      rw [← set.preimage_inter, set.image_preimage_eq_inter_range, set.inter_eq_left_iff_subset],
      exact (set.inter_subset_left _ _).trans (hU.trans (set.image_subset_range _ _)) },
    { intros x hx, rw ← (h.inj.inj_on _).mem_image_iff (set.subset_univ _) trivial, exact hU hx },
    { rw h.to_embedding.is_compact_iff_is_compact_image,
      convert hU'',
      rw [set.image_preimage_eq_inter_range, set.inter_eq_left_iff_subset],
      exact hU.trans (set.image_subset_range _ _) },
    { intros x hx, rw ← (h.inj.inj_on _).mem_image_iff (set.subset_univ _) trivial, exact hV hx },
    { rw h.to_embedding.is_compact_iff_is_compact_image,
      convert hV'',
      rw [set.image_preimage_eq_inter_range, set.inter_eq_left_iff_subset],
      exact hV.trans (set.image_subset_range _ _) } },
  { intros H U V hU hU' hU'' hV hV' hV'',
    rw [h.to_embedding.is_compact_iff_is_compact_image, ← set.image_inter h.inj],
    exact H (f '' U) (f '' V)
      (set.image_subset _ hU) (h.is_open_map _ hU') (hU''.image h.continuous)
      (set.image_subset _ hV) (h.is_open_map _ hV') (hV''.image h.continuous) }
end

lemma is_quasi_separated_iff_quasi_separated_space (s : set α) (hs : is_open s) :
  is_quasi_separated s ↔ quasi_separated_space s :=
begin
  rw ← is_quasi_separated_univ,
  convert (hs.open_embedding_subtype_coe.is_quasi_separated_iff (coe ⁻¹' s)).symm; simp
end
