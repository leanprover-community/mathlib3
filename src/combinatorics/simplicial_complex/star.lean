/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.closure

/-!
# Star in a simplicial complex
-/

open finset geometry

variables {𝕜 E : Type*}

namespace geometry.simplicial_complex
section ordered_ring
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {n : ℕ}
  {K : simplicial_complex 𝕜 E} {s t : finset E} {A B : set (finset E)}

/-- The open star of a set of faces is the union of their surfaces. Note that the star is all of the
original complex as soon as A contains the empty set. -/
def star (K : simplicial_complex 𝕜 E) (A : set (finset E)) : set (finset E) :=
{s | s ∈ K ∧ ∃ t ∈ A, t ⊆ s}

lemma star_empty : K.star ∅ = ∅ := by { unfold star, simp }

lemma star_singleton_empty : K.star {∅} = K.faces := by { unfold star, simp, refl }

lemma mem_star_singleton_iff : t ∈ K.star {s} ↔ t ∈ K ∧ s ⊆ t := by { unfold star, simp }

lemma mem_star_iff : s ∈ K.star A ↔ s ∈ K.faces ∩ ⋃ (t ∈ A), {u | t ⊆ u} :=
by { unfold star, simp }

lemma star_subset : K.star A ⊆ K.faces := λ s hs, hs.1

lemma subset_star : K.faces ∩ A ⊆ K.star A := λ s hs, ⟨hs.1, s, hs.2, subset.rfl⟩

lemma star_mono (hAB : A ⊆ B) : K.star A ⊆ K.star B := λ s ⟨hs, t, ht, hts⟩, ⟨hs, t, hAB ht, hts⟩

lemma star_up_closed : s ∈ K → t ∈ K.star A → t ⊆ s → s ∈ K.star A :=
λ hs ⟨ht, u, hu, hut⟩ hts, ⟨hs, u, hu, subset.trans hut hts⟩

lemma Union_star_eq_star : (⋃ (s ∈ A), K.star {s}) = K.star A :=
begin
  ext s,
  rw set.mem_Union₂,
  split,
  { rintro ⟨t', ht, hs, t, (htt' : t = t'), hts⟩,
    subst htt',
    exact ⟨hs, t, ht, hts⟩ },
  { rintro ⟨hs, t, ht, hts⟩,
    exact ⟨t, ht, hs, t, set.mem_singleton t, hts⟩ }
end

--Can maybe get rid of hs?
lemma star_singleton_eq_Inter_star_singleton (hs : s ∈ K) : K.star {s} = ⋂ x ∈ s, K.star {{x}} :=
begin
  ext t,
  refine ⟨_, λ h, _⟩,
  { rintro ⟨ht, u, (hu : u = s), hst⟩,
    rw hu at hst,
    exact set.mem_bInter (λ x (hx : x ∈ s), ⟨ht, {x}, set.mem_singleton {x},
      singleton_subset_iff.2 $ hst hx⟩) },
  { rw mem_star_singleton_iff,
    refine ⟨_, λ x hx, _⟩,
    { simp only [set.mem_Inter] at h,
      sorry
    },
    obtain ⟨ht, u, (hu : u = {x}), hxt⟩ := set.mem_Inter₂.1 h x hx,
    rw hu at hxt,
    exact singleton_subset_iff.1 hxt }
end

/-- The closed star of a complex `K` and a set `A` is the complex whose faces are in `K` and share a
surface with some face in `A`. -/
def Star (K : simplicial_complex 𝕜 E) (A : set (finset E)) : simplicial_complex 𝕜 E :=
K.of_subcomplex {s | s.nonempty ∧ ∃ (t ∈ A) (u ∈ K), s ⊆ u ∧ t ⊆ u}
  (λ s ⟨hs, _, u, _, hu, hsu, _⟩, K.down_closed hu hsu hs)
  (λ s t ⟨hs, u, v, hu, hv, hsv, huv⟩ hts ht, ⟨ht, u, v, hu, hv, hts.trans hsv, huv⟩)

lemma Star_le : K.Star A ≤ K := K.of_subcomplex_le _

lemma Star_bot : (⊥ : simplicial_complex 𝕜 E).Star A = ⊥ := of_subcomplex_bot _

lemma Star_empty : K.Star ∅ = ⊥ := ext _ _ $ set.eq_empty_of_forall_not_mem $ by simp [Star]

lemma Star_singleton_empty : K.Star {∅} = K :=
begin
  ext s,
  refine ⟨_, λ hs, ⟨K.nonempty hs, ∅, rfl, s, hs, subset.rfl, empty_subset _⟩⟩,
  rintro ⟨hs, t, (ht : t = ∅), u, hu, hsu, htu⟩,
  exact K.down_closed hu hsu hs,
end

lemma mem_Star_singleton_iff : t ∈ K.Star {s} ↔ t.nonempty ∧ ∃ u ∈ K, t ⊆ u ∧ s ⊆ u :=
by simp [Star]

/-- The closed star of a set is the closure of its open star. -/
lemma Star_eq_closure_star : K.Star A = K.closure (K.star A) :=
begin
  ext s,
  split,
  { rintro ⟨hs, t, ht, u, hu, hsu, htu⟩,
    exact ⟨K.down_closed hu hsu hs, u, ⟨hu, t, ht, htu⟩, hsu⟩ },
  { rintro ⟨hs, u, ⟨hu, t, ht, htu⟩, hsu⟩,
    exact ⟨K.nonempty hs, t, ht, u, hu, hsu, htu⟩ }
end

lemma subset_Star : K.faces ∩ A ⊆ (K.Star A).faces :=
λ s ⟨hs, hsA⟩, ⟨K.nonempty hs, s, hsA, s, hs, subset.rfl, subset.rfl⟩

lemma star_subset_Star : K.star A ⊆ (K.Star A).faces :=
λ s ⟨hs, t, ht, hts⟩, ⟨K.nonempty hs, t, ht, s, hs, subset.rfl, hts⟩

lemma Star_mono (hAB : A ⊆ B) : K.Star A ≤ K.Star B :=
by { rw [Star_eq_closure_star, Star_eq_closure_star], exact closure_mono (star_mono hAB) }

lemma mem_facets_Star_iff : s ∈ (K.Star A).facets ↔ s ∈ K.facets ∧ ∃ t ∈ A, t ⊆ s :=
begin
  split,
  { rintro ⟨⟨hs, t, ht, u, hu, hsu, htu⟩, hsmax⟩,
    have := hsmax ⟨hs.mono hsu, t, ht, u, hu, subset.rfl, htu⟩ hsu,
    subst this,
    exact ⟨⟨hu, λ v hv hsv, hsmax (star_subset_Star ⟨hv, t, ht, htu.trans hsv⟩) hsv⟩, t, ht, htu⟩ },
  { rintro ⟨hs, t, ht, hts⟩,
    exact ⟨⟨K.nonempty hs.1, t, ht, s, hs.1, subset.rfl, hts⟩, λ u hu, hs.2 $ Star_le hu⟩ }
end

protected lemma pure.Star (hK : K.pure n) : (K.Star A).pure n :=
⟨λ s hs, hK.1 $ Star_le hs, λ s hs, hK.2 (mem_facets_Star_iff.1 hs).1⟩

end ordered_ring
end geometry.simplicial_complex
