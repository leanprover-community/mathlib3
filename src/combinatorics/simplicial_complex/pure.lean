/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.basic

/-!
# Pure simplicial complexes
-/

open geometry set
open_locale classical

namespace geometry.simplicial_complex
variables {𝕜 E : Type*} [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {a b m n : ℕ}
  {S : simplicial_complex 𝕜 E} {s : finset E}

/-- A simplicial complex is pure of dimension `n` iff all its facets have dimension `n`. -/
def pure (S : simplicial_complex 𝕜 E) (n : ℕ) : Prop := ∀ ⦃s : finset E⦄, s ∈ S.facets → s.card = n

-- def full_dimensional (S : simplicial_complex 𝕜 E) : Prop := S.pure (S.dim + 1) hS,

lemma bot_pure (n : ℕ) : (⊥ : simplicial_complex 𝕜 E).pure n :=
λ s hs, (facets_bot.subset hs).elim

variables [finite_dimensional ℝ E]

lemma pure.card_le (hS : S.pure n) (hs : s ∈ S.faces) : s.card ≤ n :=
begin
  obtain ⟨Y, hY, hsY⟩ := subfacet hs,
  rw ← hS hY,
  exact finset.card_le_of_subset hsY,
end

lemma pureness_unique_of_nonempty (hS : S.faces.nonempty) (ha : S.pure a) (hb : S.pure b) :
  a = b :=
begin
  obtain ⟨s, hs⟩ := hS,
  obtain ⟨Y, hY, hYs⟩ := subfacet hs,
  rw [←ha hY, ←hb hY],
end

lemma pureness_def' (hSnonempty : S.faces.nonempty) (hS : S.pure n) : S.pureness = n :=
pureness_unique_of_nonempty hSnonempty (pureness_def ⟨_, hS⟩) hS

lemma facet_iff_dimension_eq_pureness (hS : S.pure n) (hs : s ∈ S.faces) :
  s ∈ S.facets ↔ s.card = n :=
begin
  refine ⟨λ hsfacet, hS hsfacet, λ hscard, ⟨hs, λ Y hY hsY, finset.eq_of_subset_of_card_le hsY _⟩⟩,
  rw hscard,
  exact face_card_le_pureness hS hY,
end

/-- A simplicial complex is pure iff there exists n such that all faces are subfaces of some
(n - 1)-dimensional face. -/
lemma pure_iff :
  S.pure ↔ ∃ n : ℕ, ∀ {s}, s ∈ S.faces → ∃ {Y}, Y ∈ S.faces ∧ finset.card Y = n ∧ s ⊆ Y :=
begin
  split,
  { rintro hS,
    use S.pureness,
    rintro s hs,
    obtain ⟨Y, hY, hsY⟩ := subfacet hs,
    exact ⟨Y, facets_subset hY, pureness_def hS hY, hsY⟩ },
  { rintro ⟨n, hS⟩,
    use n,
    rintro s ⟨hs, hsmax⟩,
    obtain ⟨Y, hY, hYcard, hsY⟩ := hS hs,
    rw hsmax hY hsY,
    exact hYcard }
end

lemma facets_subset_facets_of_pureness_eq_pureness_of_subcomplex {S₁ S₂ : simplicial_complex 𝕜 E}
  (hS : S₁.faces ⊆ S₂.faces) (hS₁ : S₁.pure n) (hS₂ : S₂.pure n) :
  S₁.facets ⊆ S₂.facets :=
begin
  rintro s hs,
  use hS hs.1,
  rintro Y hY hsY,
  apply finset.eq_of_subset_of_card_le hsY,
  rw hS₁ hs,
  exact face_card_le_pureness hS₂ hY,
end

end geometry.simplicial_complex
