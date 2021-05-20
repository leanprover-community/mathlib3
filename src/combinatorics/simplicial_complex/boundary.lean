import combinatorics.simplicial_complex.link
import combinatorics.simplicial_complex.subdivision

namespace affine
open set
variables {m n : ℕ} {E : Type*} [normed_group E] [normed_space ℝ E] {S : simplicial_complex E}
  {X Y : finset E} {A : set (finset E)}

def simplicial_complex.on_boundary (S : simplicial_complex E) (X : finset E) :
  Prop :=
∃ (Z ∈ S.faces), X ⊂ Z ∧ ∀ {Z'}, Z' ∈ S.faces → X ⊂ Z' → Z = Z'

def simplicial_complex.boundary (S : simplicial_complex E) :
  simplicial_complex E :=
simplicial_complex.of_surcomplex
  {X | ∃ Y ∈ S.faces, X ⊆ Y ∧ S.on_boundary Y}
  (λ X ⟨Y, hY, hXY, _⟩, S.down_closed hY hXY)
  (λ X W ⟨Y, hY, hXY, Z⟩ hWX, ⟨Y, hY, subset.trans hWX hXY, Z⟩)

lemma boundary_empty (hS : S.faces = ∅) :
  S.boundary.faces = ∅ :=
begin
  unfold simplicial_complex.boundary,
  simp,
  rw hS,
  simp,
end

lemma boundary_singleton_empty (hS : S.faces = {∅}) :
  S.boundary.faces = ∅ :=
begin
  ext X,
  unfold simplicial_complex.boundary simplicial_complex.on_boundary,
  simp,
  rw hS,
  rintro _ (rfl : _ = ∅) XY Y (rfl : _ = ∅) t,
  apply (t.2 (empty_subset _)).elim,
end

lemma boundary_subset :
  S.boundary.faces ⊆ S.faces :=
λ X ⟨Y, hY, hXY, _⟩, S.down_closed hY hXY

lemma mem_boundary_iff_subset_unique_facet :
  X ∈ S.boundary.faces ↔ ∃ {Y Z}, Y ∈ S.faces ∧ Z ∈ S.facets ∧ X ⊆ Y ∧ Y ⊂ Z ∧
  ∀ {Z'}, Z' ∈ S.faces → Y ⊂ Z' → Z = Z' :=
begin
  split,
  { rintro ⟨Y, hY, hXY, Z, hZ, hYZ, hZunique⟩,
    suffices hZ' : Z ∈ S.facets,
    { exact ⟨Y, Z, hY, hZ', hXY, hYZ, (λ Z', hZunique)⟩ },
    use hZ,
    rintro Z' hZ' hZZ',
    exact hZunique hZ' ⟨finset.subset.trans hYZ.1 hZZ',
      (λ hZ'Y, hYZ.2 (finset.subset.trans hZZ' hZ'Y))⟩ },
  { rintro ⟨Y, Z, hY, hZ, hXY, hYZ, hZunique⟩,
    refine ⟨Y, hY, hXY, Z, hZ.1, hYZ, λ Z', hZunique⟩ }
end

lemma facets_disjoint_boundary :
  disjoint S.facets S.boundary.faces :=
begin
  rintro X ⟨⟨hX, hXunique⟩, ⟨Y, hY, hXY, Z, hZ, hYZ, hZunique⟩⟩,
  apply hYZ.2,
  rw ← hXunique hZ (subset.trans hXY hYZ.1),
  exact hXY,
end

lemma boundary_facet_iff :
  X ∈ S.boundary.facets ↔ S.on_boundary X :=
begin
  split,
  { rintro ⟨⟨Y, hY, XY, Z, hZ, hYZ, hZunique⟩, hXmax⟩,
    refine ⟨Z, hZ, finset.ssubset_of_subset_of_ssubset XY hYZ, λ Z', _⟩,
    have hX' : Y ∈ S.boundary.faces,
    { refine ⟨_, hY, subset.refl _, _, hZ, hYZ, λ Z', hZunique⟩ },
    have hXX' := hXmax hX' XY,
    subst hXX',
    apply hZunique },
  { rintro ⟨Y, hY, hXY, hYunique⟩,
    refine ⟨⟨X, S.down_closed hY hXY.1, subset.refl _, _, hY, hXY, λ Y', hYunique⟩, _⟩,
    rintro V ⟨W, hW, hVW, Z, hZ, hWZ, hZunique⟩ hXV,
    apply finset.subset.antisymm hXV,
    classical,
    by_contra hVX,
    have := hYunique (S.down_closed hW hVW) ⟨hXV, hVX⟩,
    subst this,
    have := hYunique hZ ⟨subset.trans hXV (subset.trans hVW hWZ.1),
      λ hZX, hWZ.2 (subset.trans hZX (subset.trans hXV hVW))⟩,
    subst this,
    exact hWZ.2 hVW,
  }
end

lemma boundary_facet_iff' :
  X ∈ S.boundary.facets ↔ ∃ {Y}, Y ∈ S.facets ∧ X ⊂ Y ∧ ∀ {Y'}, Y' ∈ S.faces → X ⊂ Y' → Y = Y' :=
begin
  rw boundary_facet_iff,
  split,
  { rintro ⟨Y, hY, hXY, hYunique⟩,
    have hY' : Y ∈ S.facets,
    { use hY,
      rintro Y' hY' hYY',
      exact hYunique hY' (finset.ssubset_of_ssubset_of_subset hXY hYY'),
    },
    exact ⟨Y, hY', hXY, (λ Y', hYunique)⟩ },
  { rintro ⟨Y, hY, hXY, hYunique⟩,
    exact ⟨Y, hY.1, hXY, (λ Y', hYunique)⟩ }
end

lemma pure_boundary_of_pure (hS : S.pure_of n) :
  S.boundary.pure_of (n - 1) :=
begin
  rintro X hX,
  obtain ⟨Y, hY, hXY, hYunique⟩ := boundary_facet_iff'.1 hX,
  cases n,
  { apply nat.eq_zero_of_le_zero,
    have hYcard : Y.card = 0 := hS hY,
    rw ←hYcard,
    exact le_of_lt (finset.card_lt_card hXY) },
  have hYcard : Y.card = n.succ := hS hY,
  have hXcard : X.card ≤ n,
  { have := finset.card_lt_card hXY,
    rw hYcard at this,
    exact nat.le_of_lt_succ this },
  have : n - X.card + X.card ≤ Y.card,
  { rw [hS hY, nat.sub_add_cancel hXcard, nat.succ_eq_add_one],
    linarith },
  obtain ⟨W, hXW, hWY, hWcard⟩ := finset.exists_intermediate_set (n - X.card) this hXY.1,
  rw nat.sub_add_cancel hXcard at hWcard,
  have hW : W ∈ S.boundary.faces,
  { have hYW : ¬Y ⊆ W,
    { have hWYcard : W.card < Y.card,
      { rw [hWcard, hS hY, nat.succ_eq_add_one],
        linarith },rintro hYW,
      have : n.succ = n := by rw [← hS hY, ← hWcard,
        finset.eq_of_subset_of_card_le hYW (le_of_lt hWYcard)],
      exact nat.succ_ne_self n this },
    refine ⟨W, S.down_closed (facets_subset hY) hWY, subset.refl W, Y, hY.1, ⟨hWY, hYW⟩, _⟩,
    rintro Z hZ hWZ,
    exact hYunique hZ ⟨subset.trans hXW hWZ.1, (λ hZX, hWZ.2 (finset.subset.trans hZX hXW))⟩ },
  rw [nat.succ_sub_one, ←hWcard, hX.2 hW hXW],
end

lemma boundary_link :
  S.boundary.link A = (S.link A).boundary :=
begin
  ext V,
  split,
  {
    rintro ⟨hVdisj, W, X, hW, ⟨Y, Z, hY, hZ, hXY, hYZ, hZunique⟩, hVX, hWX⟩,
    use V,
    split,
    {
      sorry
      /-split,
      exact (λ U hU, hVdisj hU),
      exact ⟨W, Z, hW, facets_subset hZ, subset.trans hVX (subset.trans hXY hYZ.1),
        subset.trans hWX (subset.trans hXY hYZ.1)⟩,-/
    },
    {
      /-use subset.refl V,
      use Z,
      split,
      {
        sorry --waiting for link_facet_iff. May make this lemma require more assumptions
      },
      use ⟨finset.subset.trans hVX (finset.subset.trans hXY hYZ.1),
        (λ hZV, hYZ.2 (finset.subset.trans hZV (finset.subset.trans hVX hXY)))⟩,
      rintro U ⟨hUdisj, T, R, hT, hR, hUR, hTR⟩ hVU,
      apply hZunique (S.down_closed hR hUR),-/
      sorry
    }
  },
  {
    sorry
  }
end

lemma boundary_boundary [finite_dimensional ℝ E] (hS : S.pure_of n) (hS' : ∀ {X}, X ∈ S.faces →
  (X : finset E).card = n - 1 → equiv {Y | Y ∈ S.faces ∧ X ⊆ Y} (fin 2)) :
  S.boundary.boundary.faces = ∅ :=
begin
  rw ← facets_empty_iff_faces_empty,
  apply eq_empty_of_subset_empty,
  rintro V hV,
  obtain ⟨W, hW, hVW, hWunique⟩ := boundary_facet_iff'.1 hV,
  obtain ⟨X, hX, hXV, hXunique⟩ := boundary_facet_iff'.1 hW,
  sorry
end

lemma boundary_mono {S₁ S₂ : simplicial_complex E} (hS : S₁ ≤ S₂) :
  S₁.boundary ≤ S₂.boundary :=
begin
  /-cases S₂.faces.eq_empty_or_nonempty with hS₂empty hS₂nonempty,
  {
    rw hS₂empty,
  },
  rw subdivision_iff_partition at ⊢ hS,-/
  have hspace : S₁.boundary.space = S₂.boundary.space,
  {
    sorry
  },
  /-rw subdivision_iff_partition,
  split,
  {
    sorry
  },
  use le_of_eq hspace,
  rintro X₂ ⟨Y₂, Z₂, hY₂, hZ₂, hX₂Y₂, hY₂Z₂, hZ₂max⟩,
  obtain ⟨hempty, hspace, hpartition⟩ := subdivision_iff_partition.1 hS,
  obtain ⟨F, hF, hX₂F⟩ := hpartition (S₂.down_closed hY₂ hX₂Y₂),
  use F, rw and.comm, use hX₂F,
  rintro X₁ hX₁,-/

  use hspace,
  rintro X₁ ⟨Y₁, hY₁, hX₁Y₁, Z₁, hZ₁, hY₁Z₁, hZ₁max⟩,
  cases X₁.eq_empty_or_nonempty with hX₁empty hX₁nonempty,
  {
    sorry},
  obtain ⟨X₂, hX₂, hX₁X₂⟩ := (subdivision_iff_combi_interiors_subset_combi_interiors.1 hS).2
    (S₁.down_closed hY₁ hX₁Y₁),
  obtain ⟨Y₂, hY₂, hY₁Y₂⟩ := (subdivision_iff_combi_interiors_subset_combi_interiors.1 hS).2 hY₁,
  obtain ⟨Z₂, hZ₂, hZ₁Z₂⟩ := (subdivision_iff_combi_interiors_subset_combi_interiors.1 hS).2 hZ₁,
  obtain ⟨x, hxX₁⟩ := id hX₁nonempty,
  refine ⟨X₂, ⟨Y₂, hY₂, _, Z₂, hZ₂, ⟨_, _⟩⟩,
    convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior
    (S₁.indep (S₁.down_closed hY₁ hX₁Y₁)) (S₂.indep hX₂) hX₁X₂⟩,
  { apply subset_of_combi_interior_inter_convex_hull_nonempty hX₂ hY₂,
    obtain ⟨x, hxX₁⟩ := nonempty_combi_interior_of_nonempty (S₁.indep (S₁.down_closed hY₁ hX₁Y₁))
      hX₁nonempty,
    use [x, hX₁X₂ hxX₁],
    apply convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior (S₁.indep hY₁)
      (S₂.indep hY₂) hY₁Y₂,
    exact convex_hull_mono hX₁Y₁ hxX₁.1 },
  { obtain ⟨y, hyY₁⟩ := nonempty_combi_interior_of_nonempty (S₁.indep hY₁) ⟨x, hX₁Y₁ hxX₁⟩,
    split,
    { apply subset_of_combi_interior_inter_convex_hull_nonempty hY₂ hZ₂,
      use [y, hY₁Y₂ hyY₁],
      apply convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior (S₁.indep hZ₁)
        (S₂.indep hZ₂) hZ₁Z₂,
      exact convex_hull_mono hY₁Z₁.1 hyY₁.1 },
    { rintro hZ₂Y₂,
      suffices hY₂Z₂ : ¬Y₂ ⊆ Z₂,
      { apply (hY₁Y₂ hyY₁).2,
        rw mem_combi_frontier_iff,
        use [Z₂, ⟨hZ₂Y₂, hY₂Z₂⟩],
        apply convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior (S₁.indep hZ₁)
          (S₂.indep hZ₂) hZ₁Z₂,
        exact convex_hull_mono hY₁Z₁.1 hyY₁.1 },
      rintro hY₂Z₂,
      have := finset.subset.antisymm hY₂Z₂ hZ₂Y₂,
      subst this,
      suffices h : Y₁.card = Y₂.card,
      { have := finset.card_lt_card hY₁Z₁,
        have := card_le_of_convex_hull_subset (S₁.indep hZ₁)
          (convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior (S₁.indep hZ₁)
          (S₂.indep hY₂) hZ₁Z₂),
        linarith },

      sorry
    },
  },
  {
    rintro Z' hZ' hY₂Z',
    suffices hZ₁Z' : combi_interior Z₁ ⊆ combi_interior Z',
    {
      obtain ⟨z, hzZ₁⟩ := nonempty_combi_interior_of_nonempty (S₁.indep hZ₁) ⟨x, hY₁Z₁.1 (hX₁Y₁ hxX₁)⟩,
      exact disjoint_interiors hZ₂ hZ' (hZ₁Z₂ hzZ₁) (hZ₁Z' hzZ₁),
    },

    sorry
  }
end

--other attempt using subdivision_iff_partition
lemma boundary_mono' {S₁ S₂ : simplicial_complex E} (hS : S₁ ≤ S₂) :
  S₁.boundary ≤ S₂.boundary :=
begin
  rw subdivision_iff_partition,
  obtain ⟨hempty, hspace, hpartition⟩ := subdivision_iff_partition.1 hS,
  split,
  sorry,
  split,
  sorry,
  rintro X₂ hX₂,--rintro X₂ ⟨Y₂, hY₂, hX₂Y₂, Z₂, hZ₂, hY₂Z₂, hZ₂max⟩,
  obtain ⟨F, hF, hXF⟩ := hpartition (boundary_subset hX₂),--obtain ⟨F, hF, hXF⟩ := hpartition (S₂.down_closed hY₂ hX₂Y₂),
  use F,
  rw and.comm,
  use hXF,
  rintro X₁ hX₁,
  have hX₁X₂ : combi_interior X₁ ⊆ combi_interior X₂,
  { rw hXF,
    exact subset_bUnion_of_mem hX₁ },
  sorry
end

/--
A m-simplex is on the boundary of a full dimensional complex iff it belongs to exactly one cell.
Dull?
-/
lemma boundary_subcell_iff_one_surface (hS : S.full_dimensional) (hXcard : X.card = finite_dimensional.finrank ℝ E) :
  X ∈ S.boundary.faces ↔ nat.card {Y | Y ∈ S.faces ∧ X ⊂ Y} = 1 :=
  -- It's probably a bad idea to use `nat.card` since it's incredibly underdeveloped for doing
  -- actual maths in
  -- Does this lemma need you to assume locally finite (at X)? If so, the set you care about is a
  -- subset of the set we know is finite, so we can convert to a finset and use normal card
begin
  split,
  {
    rintro ⟨Y, hY, hXY, Z, hZ, hYZ, hZunique⟩,
    have : X = Y,
    {
      sorry
    },
    sorry--rw nat.card_eq_fintype_card,
  },
  -- have aux_lemma : ∀ {a b : E}, a ≠ b → a ∉ X → b ∉ X → X ∪ {a} ∈ S.faces → X ∪ {b} ∈ S.faces →
  --   ∃ w : E → ℝ, w a < 0 ∧ ∑ y in X ∪ {a}, w y = 1 ∧ (X ∪ {a}).center_mass w id = b,
  -- {
  --   sorry
  -- },
  sorry
end

/--
A m-simplex is not on the boundary of a full dimensional complex iff it belongs to exactly two
cells.
-/
lemma not_boundary_subcell_iff_two_surfaces (hS : S.full_dimensional) (hXcard : X.card = finite_dimensional.finrank ℝ E) :
  X ∉ S.boundary.faces ↔ nat.card {Y | Y ∈ S.faces ∧ X ⊂ Y} = 2 :=
  -- It's probably a bad idea to use `nat.card` since it's incredibly underdeveloped for doing
  -- actual maths in
  -- Does this lemma need you to assume locally finite (at X)? If so, the set you care about is a
  -- subset of the set we know is finite, so we can convert to a finset and use normal card
begin
  -- have aux_lemma : ∀ {a b : E}, a ≠ b → a ∉ X → b ∉ X → X ∪ {a} ∈ S.faces → X ∪ {b} ∈ S.faces →
  --   ∃ w : E → ℝ, w a < 0 ∧ ∑ y in X ∪ {a}, w y = 1 ∧ (X ∪ {a}).center_mass w id = b,
  -- {
  --   sorry
  -- },
  sorry
end

end affine
