import combinatorics.simplicial_complex.basic
import combinatorics.simplicial_complex.finite
import combinatorics.simplicial_complex.pure
import combinatorics.simplicial_complex.link

namespace affine
open set
variables {m n : ℕ}
local notation `E` := fin m → ℝ

def simplicial_complex.on_boundary (S : simplicial_complex m) (X : finset E) : Prop :=
∃ (Z ∈ S.faces), X ⊂ Z ∧ ∀ {Z'}, Z' ∈ S.faces → X ⊂ Z' → Z = Z'

def simplicial_complex.boundary (S : simplicial_complex m) : simplicial_complex m :=
simplicial_complex.of_surcomplex
  {X | ∃ Y ∈ S.faces, X ⊆ Y ∧ S.on_boundary Y}
  (λ X ⟨Y, hY, hXY, _⟩, S.down_closed hY hXY)
  (λ X W ⟨Y, hY, hXY, Z⟩ hWX, ⟨Y, hY, subset.trans hWX hXY, Z⟩)

lemma boundary_empty {S : simplicial_complex m} (hS : S.faces = ∅) : S.boundary.faces = ∅ :=
begin
  unfold simplicial_complex.boundary,
  simp,
  rw hS,
  simp,
end

lemma boundary_singleton_empty {S : simplicial_complex m} (hS : S.faces = {∅}) :
  S.boundary.faces = ∅ :=
begin
  ext X,
  unfold simplicial_complex.boundary simplicial_complex.on_boundary,
  simp,
  rw hS,
  rintro _ (rfl : _ = ∅) XY Y (rfl : _ = ∅) t,
  apply (t.2 (empty_subset _)).elim,
end

lemma boundary_subset {S : simplicial_complex m} : S.boundary.faces ⊆ S.faces :=
  λ X ⟨Y, hY, hXY, _⟩, S.down_closed hY hXY

lemma mem_boundary_iff_subset_unique_facet {S : simplicial_complex m} {X : finset E} :
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

lemma facets_disjoint_boundary {S : simplicial_complex m} : disjoint S.facets S.boundary.faces :=
begin
  rintro X ⟨⟨hX, hXunique⟩, ⟨Y, hY, hXY, Z, hZ, hYZ, hZunique⟩⟩,
  apply hYZ.2,
  rw ← hXunique hZ (subset.trans hXY hYZ.1),
  exact hXY,
end

lemma boundary_facet_iff {S : simplicial_complex m} {X : finset E} :
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
    by_contra hVX,
    have := hYunique (S.down_closed hW hVW) ⟨hXV, hVX⟩,
    subst this,
    have := hYunique hZ ⟨subset.trans hXV (subset.trans hVW hWZ.1),
      λ hZX, hWZ.2 (subset.trans hZX (subset.trans hXV hVW))⟩,
    subst this,
    exact hWZ.2 hVW,
  }
end

lemma boundary_facet_iff' {S : simplicial_complex m} {X : finset E} :
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

lemma pure_boundary_of_pure {S : simplicial_complex m} {n : ℕ} (hS : S.pure_of n) :
  S.boundary.pure_of (n - 1) :=
begin
  cases n,
  { rw nat.zero_sub,
    rintro X hX,
    obtain ⟨Y, hY, hXY⟩ := subfacet (boundary_subset (facets_subset hX)),
    rw finset.card_eq_zero.mp (hS hY) at hXY,
    exact finset.card_eq_zero.2 (finset.subset_empty.1 hXY) },
  rintro X hX,
  obtain ⟨Y, hY, hXY, hYunique⟩ := boundary_facet_iff'.1 hX,
  have hYcard : Y.card = n.succ := hS hY,
  have hXcard : X.card ≤ n := nat.le_of_lt_succ (nat.lt_of_lt_of_le (finset.card_lt_card hXY)
    (simplex_dimension_le_pureness hS hY.1)),
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
  rw [nat.succ_sub_one, ← hWcard, hX.2 hW hXW],
end


lemma boundary_boundary {S : simplicial_complex m} (hS : S.pure_of n) (hS' : ∀ {X}, X ∈ S.faces →
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

--lemma boundary_pureness_eq_pureness_sub_one {S : simplicial_complex m} (hS : S.pure) : pureness (pure_boundary_of_pure hS) = S.pureness - 1 := sorry

lemma boundary_link {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} : --{X : finset (fin m → ℝ)}
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

def simplicial_complex.boundaryless (S : simplicial_complex m) : Prop := S.boundary.faces = ∅

lemma boundary_boundaryless_of_locally_finite {S : simplicial_complex m} (hS : S.locally_finite) :
  S.boundary.boundaryless :=
begin
  apply eq_empty_of_subset_empty,
  rintro X hX,
  sorry
  /-have := boundary_boundary hX,
  exact this.2 (hS this.1),-/
end

end affine
