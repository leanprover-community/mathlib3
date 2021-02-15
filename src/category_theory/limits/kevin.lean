import topology.subset_properties

lemma compact_iff_finite_subcover'
  {α : Type} [topological_space α] {S : set α} :
  is_compact S ↔ (∀ {ι : Type} (U : ι → set α), (∀ i, is_open (U i)) →
    S ⊆ (⋃ i, U i) → (∃ (t : set ι), t.finite ∧ S ⊆ (⋃ i ∈ t, U i))) :=
begin
  rw compact_iff_finite_subcover,
  split,
  { intros hs ι U hU hsU,
    cases hs U hU hsU with F hF,
    use [(↑F : set ι), finset.finite_to_set F],
    exact hF },
  { intros hs ι U hU hsU,
    rcases hs U hU hsU with ⟨F, hFfin, hF⟩,
    use hFfin.to_finset,
    convert hF,
    ext,
    simp }
end
