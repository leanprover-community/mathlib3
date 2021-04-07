import analysis.convex.topology

variables {E : Type*} [add_comm_group E] [vector_space ℝ E]

@[simp]
lemma convex_hull_empty :
  convex_hull (∅ : set E) = ∅ :=
(convex_empty).convex_hull_eq

lemma convex_hull_empty_iff {X : set E} : convex_hull X = ∅ ↔ X = ∅ :=
begin
  split,
  { intro h,
    rw [←set.subset_empty_iff, ← h],
    apply subset_convex_hull },
  { rintro rfl,
    simp }
end
