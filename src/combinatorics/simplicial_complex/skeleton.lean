/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.pure

/-!
# Skeletons of a simplicial complex
-/

open finset geometry

variables {𝕜 E : Type*}

namespace geometry.simplicial_complex
section ordered_ring
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {m n k : ℕ}
  {K : simplicial_complex 𝕜 E} {s t : finset E} {A : set (finset E)}

/-- The `k`-skeleton of a simplicial complex is the simplicial complex made of its simplices of
dimension less than `k`. -/
def skeleton (K : simplicial_complex 𝕜 E) (k : ℕ) : simplicial_complex 𝕜 E :=
K.of_subcomplex
  {s | s ∈ K ∧ s.card ≤ k + 1}
  (λ s ⟨hs, _⟩, hs)
  (λ s t hs hts ht, ⟨K.down_closed hs.1 hts ht, (card_le_of_subset hts).trans hs.2⟩)

lemma skeleton_le : K.skeleton k ≤ K := K.of_subcomplex_le _

lemma boundary_bot (k : ℕ) : (⊥ : simplicial_complex 𝕜 E).skeleton k = ⊥ := of_subcomplex_bot _

lemma skeleton_nonempty_iff : (K.skeleton k).faces.nonempty ↔ K.faces.nonempty :=
begin
  split,
  { exact nonempty.mono skeleton_le },
  { rintro ⟨s, hs⟩,
    exact ⟨∅, K.down_closed hs s.empty_subset, nat.zero_le _⟩ }
end

lemma pure.skeleton_of_le (hK : K.pure n) (h : k ≤ n) : (K.skeleton k).pure k :=
begin
  rintro s ⟨⟨hs, hscard⟩, hsmax⟩,
  obtain ⟨t, ht, hst, htcard⟩ := hK.exists_face_of_card_le (add_le_add_right h 1) hs hscard,
  rwa hsmax ⟨ht, htcard.le⟩ hst,
end

end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] [finite_dimensional 𝕜 E]
  {m n k : ℕ} {K : simplicial_complex 𝕜 E} {s t : finset E} {A : set (finset E)}

lemma pure.skeleton (hK : K.pure n) : (K.skeleton k).pure (min k n) :=
begin
  obtain hn | hn := le_total k n,
  { rw min_eq_left hn,
    exact hK.skeleton_of_le hn },
  { rw min_eq_right hn,
    rintro s hs,
    obtain ⟨t, ht, hst⟩ := subfacet (skeleton_le hs.1),
    rw hs.2 ⟨facets_subset ht, (hK ht).le.trans (add_le_add_right hn _)⟩ hst,
    exact hK ht }
end

end linear_ordered_field
end geometry.simplicial_complex
