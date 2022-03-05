import algebraic_geometry.morphisms.affine

open category_theory category_theory.limits opposite topological_space

namespace algebraic_geometry

lemma is_affine_of_closed_embedding {X Y : Scheme} (f : X ⟶ Y) [is_affine Y]
  (hf : closed_embedding f.1.base) : is_affine X :=
begin
  have : ∀ x, ∃ (s : Y.presheaf.obj (op ⊤)) (U : X.affine_opens),
    f.1.base x ∈ Y.basic_open s ∧ @Scheme.basic_open X ⊤ (f.1.c.app (op ⊤) s) ≤ U.1,
  { intro x,
    obtain ⟨_, ⟨U, hU : is_affine_open U, rfl⟩, hxU, -⟩ :=
      (is_basis_affine_open X).exists_subset_of_mem_open
      (show x ∈ (set.univ : set X.carrier), from trivial) is_open_univ,
    obtain ⟨V, hV, hV'⟩ := hf.to_inducing.is_open_iff.mp U.prop,
    rw ← hV' at hxU,
    obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hr⟩ :=
      (is_basis_basic_open Y).exists_subset_of_mem_open (show f.1.base x ∈ _, from hxU) hV,
    refine ⟨r, ⟨U, hU⟩, hxr, _⟩,
    rw ← Scheme.preimage_basic_open,
    have := set.preimage_mono hr, rw hV' at this, exact this },
  choose s U hs hU using this,
  have := hf.closed_range,
  obtain ⟨ι, t, ht, ht'⟩ := (is_basis_basic_open Y).open_eq_Union hf.closed_range.1,
  have : ∀ i : ι, ∃ r : Y.presheaf.obj (op ⊤), (Y.basic_open r).1 = t i,
  { intro i, rcases ht' i with ⟨_, ⟨r, rfl⟩, e⟩, exact ⟨r, e⟩ },
  choose t' ht' using this,
  let r : X.carrier ⊕ ι → Y.presheaf.obj (op ⊤) := sum.elim s t',
  apply is_affine_of_span_top_of_is_affine_open X (f.1.c.app (op ⊤) '' set.range r),
  { rw [← ideal.map_span, ← ideal.map_top (f.1.c.app (op ⊤))],
    congr' 1,
    rw [← (top_is_affine_open Y).basic_open_union_eq_self_iff, eq_top_iff],
    rintro x -,
    erw opens.mem_supr,
    by_cases x ∈ set.range f.1.base,
    { obtain ⟨x, rfl⟩ := h, exact ⟨⟨_, sum.inl _, rfl⟩, hs _⟩ },
    { rw [← set.mem_compl_iff, ht, set.mem_Union] at h,
      obtain ⟨i, hi⟩ := h, rw ← ht' at hi, exact ⟨⟨_, sum.inr _, rfl⟩, hi⟩ } },
  { rintro ⟨_, _, ⟨i|i, rfl⟩, rfl⟩; dsimp only [r, sum.elim],
      have := inf_eq_right.mpr (hU i),
      { convert (U i).2.basic_open_is_affine
          (X.presheaf.map (hom_of_le le_top).op $ (f.val.c.app (op ⊤)) (s i)) using 1,
        rw Scheme.basic_open_res,
        exact (inf_eq_right.mpr (hU i)).symm },
      { convert bot_is_affine_open X,
        rw ← Scheme.preimage_basic_open,
        ext1,
        refine @set.preimage_eq_empty _ _ f.1.base _ (eq_bot_iff.mp _),
        apply set.subset_compl_iff_disjoint.mp,
        rw [ht', ht],
        exact set.subset_Union _ _ } }
end

end algebraic_geometry
