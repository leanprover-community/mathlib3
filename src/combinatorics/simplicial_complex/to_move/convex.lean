import analysis.convex.topology

variables {E : Type*} [add_comm_group E] [vector_space ℝ E] {X Y : set E}

@[simp]
lemma convex_hull_empty :
  convex_hull (∅ : set E) = ∅ :=
(convex_empty).convex_hull_eq

@[simp]
lemma convex_hull_empty_iff :
  convex_hull X = ∅ ↔ X = ∅ :=
begin
  split,
  { intro h,
    rw [←set.subset_empty_iff, ←h],
    exact subset_convex_hull _ },
  { rintro rfl,
    exact convex_hull_empty }
end
