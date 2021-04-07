import combinatorics.simplicial_complex.basic

namespace affine
open set
variables {m n : ℕ}
local notation `E` := fin m → ℝ
variables {S : simplicial_complex m}

open_locale classical

/--
A simplicial complex is pure of dimension n iff all its facets have dimension n.
-/
def simplicial_complex.pure_of (S : simplicial_complex m) (n : ℕ) : Prop :=
  ∀ ⦃X⦄, X ∈ S.facets → (X : finset _).card = n

/--
A simplicial complex is pure iff all its facets have the same dimension.
-/
def simplicial_complex.pure (S : simplicial_complex m) : Prop := ∃ n : ℕ, S.pure_of n

/--
The pureness of a pure simplicial complex is the cardinality of its facets. Set to 0 for non pure
complexes.
-/
noncomputable def simplicial_complex.pureness (S : simplicial_complex m) : ℕ :=
  if hS : S.pure then nat.find hS else 0

lemma pureness_def {S : simplicial_complex m} (hS : S.pure) : S.pure_of S.pureness :=
begin
  unfold simplicial_complex.pureness,
  rw dif_pos hS,
  exact nat.find_spec hS,
end

lemma pureness_unique_of_nonempty {S : simplicial_complex m} {a b : ℕ} (hS : S.faces.nonempty)
  (ha : S.pure_of a) (hb : S.pure_of b) :
  a = b :=
begin
  obtain ⟨X, hX⟩ := hS,
  obtain ⟨Y, hY, hYX⟩ := subfacet hX,
  rw [←ha hY, ←hb hY],
end

lemma pureness_def' {S : simplicial_complex m} (hSnonempty : S.faces.nonempty) (hS : S.pure_of n) :
  S.pureness = n :=
pureness_unique_of_nonempty hSnonempty (pureness_def ⟨_, hS⟩) hS

lemma simplex_dimension_le_pureness {S : simplicial_complex m} {n : ℕ} (hS : S.pure_of n)
  {X : finset (fin m → ℝ)} : X ∈ S.faces → X.card ≤ n :=
begin
  rintro hX,
  obtain ⟨Y, hY, hXY⟩ := subfacet hX,
  rw ← hS hY,
  exact finset.card_le_of_subset hXY,
end

lemma facet_iff_dimension_eq_pureness {S : simplicial_complex m} (hS : S.pure)
  {X : finset (fin m → ℝ)} (hX : X ∈ S.faces) :
  X ∈ S.facets ↔ X.card = S.pureness :=
begin
  refine ⟨λ t, pureness_def hS t, λ hXcard, _⟩,
  { refine ⟨hX, λ Y hY hXY, finset.eq_of_subset_of_card_le hXY _⟩,
    rw hXcard,
    exact simplex_dimension_le_pureness (pureness_def hS) hY }
end

/--
A simplicial complex is pure iff there exists n such that all faces are subfaces of some
(n - 1)-dimensional face.
-/
lemma pure_iff {S : simplicial_complex m} : S.pure ↔ ∃ n : ℕ, ∀ {X}, X ∈ S.faces →
  ∃ {Y}, Y ∈ S.faces ∧ finset.card Y = n ∧ X ⊆ Y :=
begin
  split,
  { rintro hS,
    use S.pureness,
    rintro X hX,
    obtain ⟨Y, hY, hXY⟩ := subfacet hX,
    exact ⟨Y, facets_subset hY, pureness_def hS hY, hXY⟩ },
  { rintro ⟨n, hS⟩,
    use n,
    rintro X ⟨hX, hXmax⟩,
    obtain ⟨Y, hY, hYcard, hXY⟩ := hS hX,
    rw hXmax hY hXY,
    exact hYcard, }
end

lemma pure_of_empty {S : simplicial_complex m} (h : S.faces = {∅}) : S.pure :=
begin
  use 0,
  rintro X hX,
  have := facets_subset hX,
  rw h at this,
  change X = ∅ at this,
  rw this,
  exact finset.card_empty,
end

lemma facets_subset_facets_of_pureness_eq_pureness_of_subcomplex {S₁ S₂ : simplicial_complex m}
  (hS : S₁.faces ⊆ S₂.faces) (hS₁ : S₁.pure_of n) (hS₂ : S₂.pure_of n) : S₁.facets ⊆ S₂.facets :=
begin
  rintro X hX,
  use hS hX.1,
  rintro Y hY hXY,
  have : Y.card ≤ X.card,
  { rw hS₁ hX,
    exact simplex_dimension_le_pureness hS₂ hY },
  exact finset.eq_of_subset_of_card_le hXY this,
end

def simplicial_complex.full_dimensional (S : simplicial_complex m) : Prop := S.pure_of (m + 1)

end affine
