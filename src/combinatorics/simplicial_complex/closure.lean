/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.pure
import order.antichain

/-!
# Closure of a simplicial complex
-/

open_locale classical affine big_operators
open finset geometry

variables {𝕜 E : Type*}

namespace geometry.simplicial_complex
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {m n : ℕ}
  {K : simplicial_complex 𝕜 E} {x : E} {s t : finset E} {A B : set (finset E)}

/-- The closure of a set of faces is the set of their subfaces. -/
def closure (K : simplicial_complex 𝕜 E) (A : set (finset E)) :
  simplicial_complex 𝕜 E :=
K.of_subcomplex
  {s | s ∈ K ∧ ∃ t ∈ A, s ⊆ t}
  (λ s ⟨hs, _⟩, hs)
  (λ s t ⟨hs, u, hu, hsu⟩ hts ht, ⟨K.down_closed hs hts ht, u, hu, hts.trans hsu⟩)

lemma closure_le : K.closure A ≤ K := K.of_subcomplex_le _

lemma closure_bot : (⊥ : simplicial_complex 𝕜 E).closure A = ⊥ := of_subcomplex_bot _

lemma closure_empty : K.closure ∅ = ⊥ := eq_bot_of_forall_not_mem _ $ λ s ⟨hs, t, ht, hst⟩, ht

--Homonymy problem
lemma closure_singleton (hx : x ∈ K.vertices) : (K.closure {{x}}).faces = {{x}} :=
begin
  ext s,
  split,
  { rintro ⟨hs, t, (rfl : t = {x}), hsx⟩,
    exact (subset_singleton_iff.1 hsx).resolve_left (K.nonempty hs).ne_empty },
  { rintro (rfl : s = {x}),
    exact ⟨hx, {x}, rfl, subset.refl _⟩ }
end

--Homonymy problem
lemma mem_closure_singleton_iff : t ∈ K.closure {s} ↔ t ∈ K ∧ t ⊆ s :=
begin
  split,
  { rintro ⟨ht, u, (rfl : u = s), htu⟩,
    exact ⟨ht, htu⟩ },
  { rintro ⟨ht, hts⟩,
    exact ⟨ht, s, rfl, hts⟩ }
end

--Homonymy problem
lemma faces_subset_closure : K.faces ∩ A ⊆ (K.closure A).faces :=
λ s hs, ⟨hs.1, s, hs.2, subset.refl _⟩

lemma closure_mono (hAB : A ⊆ B) : K.closure A ≤ K.closure B :=
λ s ⟨hs, t, ht, hst⟩, ⟨hs, t, hAB ht, hst⟩

lemma facets_closure_eq (hA : A ⊆ K.faces) (hAanti : is_antichain (⊆) A) :
  (K.closure A).facets = A :=
begin
  ext s,
  split,
  { rintro ⟨⟨hs, t, ht, hst⟩, hsmax⟩,
    rw hsmax ⟨hA ht, t, ht, subset.refl _⟩ hst,
    exact ht },
  { rintro hs,
    refine ⟨⟨hA hs, s, hs, subset.refl _⟩, _⟩,
    rintro t ⟨ht, u, hu, htu⟩ hst,
    refine hst.antisymm _,
    rwa hAanti.eq_of_related hs hu (hst.trans htu) }
end

lemma pure.closure (hK : K.pure n) (hA : ∀ W ∈ A, ∃ s ∈ A, s ∈ K ∧ (s : finset E).card = m) :
  (K.closure A).pure m :=
begin
  sorry
end

end geometry.simplicial_complex
