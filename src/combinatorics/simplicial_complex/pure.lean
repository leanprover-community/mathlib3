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

variables {𝕜 E : Type*}

namespace geometry.simplicial_complex
section ordered_ring
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {a b m n : ℕ}
  {K : simplicial_complex 𝕜 E} {s : finset E}

/-- A simplicial complex is pure of dimension `n` iff all its facets have dimension `n`. -/
def pure (K : simplicial_complex 𝕜 E) (n : ℕ) : Prop := ∀ ⦃s : finset E⦄, s ∈ K.facets → s.card = n

-- def full_dimensional (S : simplicial_complex 𝕜 E) : Prop := K.pure (S.dim + 1) hK,

lemma bot_pure (n : ℕ) : (⊥ : simplicial_complex 𝕜 E).pure n :=
λ s hs, (facets_bot.subset hs).elim

end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] [finite_dimensional 𝕜 E]
  {a b m n : ℕ} {K : simplicial_complex 𝕜 E} {s : finset E}

lemma pure.card_le (hK : K.pure n) (hs : s ∈ K) : s.card ≤ n :=
begin
  obtain ⟨t, ht, hst⟩ := subfacet hs,
  rw ←hK ht,
  exact finset.card_le_of_subset hst,
end

lemma pure_unique_of_nonempty (hK : K.faces.nonempty) (ha : K.pure a) (hb : K.pure b) : a = b :=
begin
  obtain ⟨s, hs⟩ := hK,
  obtain ⟨t, ht, hts⟩ := subfacet hs,
  rw [←ha ht, ←hb ht],
end

lemma facet_iff_dimension_eq_pureness (hK : K.pure n) (hs : s ∈ K) : s ∈ K.facets ↔ s.card = n :=
begin
  refine ⟨λ hsfacet, hK hsfacet, λ hscard, ⟨hs, λ t ht hst, finset.eq_of_subset_of_card_le hst _⟩⟩,
  rw hscard,
  exact hK.card_le ht,
end

/-- A simplicial complex is pure iff there exists n such that all faces are subfaces of some
(n - 1)-dimensional face. -/
lemma pure_iff : K.pure n ↔ ∀ ⦃s⦄, s ∈ K → ∃ ⦃t⦄, t ∈ K ∧ finset.card t = n ∧ s ⊆ t :=
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
  rw hK₁ hs,
  exact hK₂.card_le ht,
end

end linear_ordered_field
end geometry.simplicial_complex
