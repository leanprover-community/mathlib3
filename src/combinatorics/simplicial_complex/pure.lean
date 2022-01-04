/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.basic
import data.finset.slice

/-!
# Pure simplicial complexes
-/

open geometry set

variables {𝕜 E : Type*}

namespace geometry.simplicial_complex
section ordered_ring
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {a b n k : ℕ}
  {K : simplicial_complex 𝕜 E} {s : finset E}

/-- A simplicial complex is pure of dimension `n` iff all its faces have dimension less `n` and its
facets have dimension `n`. -/
def pure (K : simplicial_complex 𝕜 E) (n : ℕ) : Prop :=
(∀ ⦃s : finset E⦄, s ∈ K → s.card ≤ n + 1) ∧ K.facets.sized (n + 1)

-- def full_dimensional (S : simplicial_complex 𝕜 E) : Prop := K.pure (S.dim + 1) hK,


lemma pure.card_le (hK : K.pure n) (hs : s ∈ K) : s.card ≤ n + 1 := hK.1 hs
lemma pure.sized_facets (hK : K.pure n) : K.facets.sized (n + 1) := hK.2

lemma bot_pure (n : ℕ) : (⊥ : simplicial_complex 𝕜 E).pure n := ⟨λ s hs, hs.elim, λ s hs, hs.1.elim⟩

lemma pure.exists_facet (hK : K.pure n) (hs : s ∈ K) : ∃ t ∈ K.facets, s ⊆ t :=
begin
  sorry
end

lemma pure.exists_face_of_card_le (hK : K.pure n) (h : k ≤ n + 1) (hs : s ∈ K)
  (hcard : s.card ≤ k) :
  ∃ t ∈ K, s ⊆ t ∧ t.card = k :=
begin
  by_cases H : s ∈ K.facets,
  { exact ⟨s, hs, subset.rfl, hcard.antisymm $ h.trans (hK.2 H).ge⟩ },
  {
    unfold facets at H,
    simp at H,
    sorry,
  }
end

lemma pure_unique (hK : K.faces.nonempty) (ha : K.pure a) (hb : K.pure b) : a = b :=
begin
  obtain ⟨s, hs⟩ := hK,
  obtain ⟨t, ht, hts⟩ := ha.exists_facet hs,
  exact add_right_cancel ((ha.2 ht).symm.trans $ hb.2 ht),
end

lemma pure.mem_facets_iff (hK : K.pure n) (hs : s ∈ K) : s ∈ K.facets ↔ s.card = n + 1 :=
⟨λ hsfacet, hK.2 hsfacet, λ hscard, ⟨hs, λ t ht hst,
  finset.eq_of_subset_of_card_le hst $ (hK.card_le ht).trans hscard.ge⟩⟩

/-- A simplicial complex is pure iff there exists `n` such that all faces are subfaces of some
`n`-dimensional face. -/
lemma pure_iff : K.pure n ↔ ∀ ⦃s⦄, s ∈ K → ∃ t ∈ K, finset.card t = n + 1 ∧ s ⊆ t :=
begin
  refine ⟨λ hK s hs, _, λ hK s hs, _⟩,
  { obtain ⟨t, ht, hst⟩ := subfacet hs,
    exact ⟨t, ht.1, hK ht, hst⟩ },
  { obtain ⟨t, ht, htcard, hst⟩ := hK hs.1,
    rw hs.2 ht hst,
    exact htcard }
end

lemma facets_mono {K₁ K₂ : simplicial_complex 𝕜 E} (h : K₁ ≤ K₂) (hK₁ : K₁.pure n)
  (hK₂ : K₂.pure n) :
  K₁.facets ⊆ K₂.facets :=
begin
  refine λ s hs, ⟨h hs.1, λ t ht hst, finset.eq_of_subset_of_card_le hst _⟩,
  rw hK₁.2 hs,
  exact hK₂.card_le ht,
end

end ordered_ring
end geometry.simplicial_complex
