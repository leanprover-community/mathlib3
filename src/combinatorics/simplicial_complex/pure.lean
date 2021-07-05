/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.basic

namespace affine
open set
open_locale classical
variables {a b m n : ℕ} {E : Type*} [normed_group E] [normed_space ℝ E] {S : simplicial_complex E}
  {X : finset E}

/--
A simplicial complex is pure of dimension n iff all its facets have dimension n.
-/
def simplicial_complex.pure_of (S : simplicial_complex E) (n : ℕ) :
  Prop :=
∀ ⦃X⦄, X ∈ S.facets → (X : finset _).card = n

/--
A simplicial complex is pure iff all its facets have the same dimension.
-/
def simplicial_complex.pure (S : simplicial_complex E) :
  Prop :=
∃ n : ℕ, S.pure_of n

def simplicial_complex.full_dimensional (S : simplicial_complex E) :
  Prop :=
S.pure_of (S.dim + 1)

/--
The pureness of a pure simplicial complex is the cardinality of its facets. Set to 0 for non pure
complexes.
-/
noncomputable def simplicial_complex.pureness (S : simplicial_complex E) :
  ℕ :=
if hS : S.pure then nat.find hS else 0

lemma pureness_def (hS : S.pure) :
  S.pure_of S.pureness :=
begin
  unfold simplicial_complex.pureness,
  rw dif_pos hS,
  exact nat.find_spec hS,
end

lemma pure_of_empty (h : S.faces = {∅}) :
  S.pure :=
begin
  use 0,
  rintro X hX,
  have := facets_subset hX,
  rw h at this,
  change X = ∅ at this,
  rw this,
  exact finset.card_empty,
end

variables [finite_dimensional ℝ E]

lemma face_card_le_pureness (hS : S.pure_of n) (hX : X ∈ S.faces) :
  X.card ≤ n :=
begin
  obtain ⟨Y, hY, hXY⟩ := subfacet hX,
  rw ← hS hY,
  exact finset.card_le_of_subset hXY,
end

lemma pureness_unique_of_nonempty (hS : S.faces.nonempty)
  (ha : S.pure_of a) (hb : S.pure_of b) :
  a = b :=
begin
  obtain ⟨X, hX⟩ := hS,
  obtain ⟨Y, hY, hYX⟩ := subfacet hX,
  rw [←ha hY, ←hb hY],
end

lemma pureness_def' (hSnonempty : S.faces.nonempty) (hS : S.pure_of n) :
  S.pureness = n :=
pureness_unique_of_nonempty hSnonempty (pureness_def ⟨_, hS⟩) hS

lemma facet_iff_dimension_eq_pureness (hS : S.pure_of n) (hX : X ∈ S.faces) :
  X ∈ S.facets ↔ X.card = n :=
begin
  refine ⟨λ hXfacet, hS hXfacet, λ hXcard, ⟨hX, λ Y hY hXY, finset.eq_of_subset_of_card_le hXY _⟩⟩,
  rw hXcard,
  exact face_card_le_pureness hS hY,
end

/--
A simplicial complex is pure iff there exists n such that all faces are subfaces of some
(n - 1)-dimensional face.
-/
lemma pure_iff :
  S.pure ↔ ∃ n : ℕ, ∀ {X}, X ∈ S.faces → ∃ {Y}, Y ∈ S.faces ∧ finset.card Y = n ∧ X ⊆ Y :=
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
    exact hYcard }
end

lemma facets_subset_facets_of_pureness_eq_pureness_of_subcomplex {S₁ S₂ : simplicial_complex E}
  (hS : S₁.faces ⊆ S₂.faces) (hS₁ : S₁.pure_of n) (hS₂ : S₂.pure_of n) :
  S₁.facets ⊆ S₂.facets :=
begin
  rintro X hX,
  use hS hX.1,
  rintro Y hY hXY,
  apply finset.eq_of_subset_of_card_le hXY,
  rw hS₁ hX,
  exact face_card_le_pureness hS₂ hY,
end

end affine
