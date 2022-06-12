/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.link

/-!
# Erasing a vertex in a simplicial complex
-/

open finset geometry

variables {𝕜 E : Type*}

namespace geometry.simplicial_complex
variables [ordered_ring 𝕜] [add_comm_group E] [decidable_eq E] [module 𝕜 E]
  {S : simplicial_complex 𝕜 E} {A : set (finset E)}

/--
The erasure of a simplicial complex S and a set A is the subcomplex obtained after removing all
faces having a vertex in A.
-/
def erasure (S : simplicial_complex 𝕜 E) (A : set (finset E)) : simplicial_complex 𝕜 E :=
S.of_subcomplex
  {X | X ∈ S.faces ∧ ∀ ⦃W⦄, W ∈ A → disjoint W X}
  (λ X hX, hX.1)
  (λ X Y ⟨hX, hXA⟩ hYX hY,
    ⟨S.down_closed hX hYX hY, λ Z hZ,finset.disjoint_of_subset_right hYX (hXA hZ)⟩)
/-Previous def
def simplicial_complex.erasure (S : simplicial_complex 𝕜 E) (A : set (finset E)) :
  simplicial_complex 𝕜 E :=
simplicial_complex.of_subcomplex
  {X | X ∈ S.faces ∧ ∀ {Y}, Y ∈ A → disjoint X Y}
  (λ X hX, hX.1)
  (λ X Y ⟨hX, hXA⟩ hYX,
    ⟨S.down_closed hX hYX, λ Z hZ, finset.disjoint_of_subset_left hYX (hXA hZ)⟩)-/

lemma erasure_subset : (S.erasure A).faces ⊆ S.faces := λ X hX, hX.1

lemma link_eq_erasure_Star : S.link A = (S.Star A).erasure A :=
begin
  ext X,
  split,
  { rintro ⟨hX, hXdisj, hXStar⟩,
    exact ⟨⟨hX, hXStar⟩, λ r hr, disjoint_coe.1 $ hXdisj hr⟩ },
  { rintro ⟨⟨hX, hXStar⟩, hXdisj⟩,
    exact ⟨hX, λ r hr, disjoint_coe.2 $ hXdisj hr, hXStar⟩ }
end

lemma erasure_and_closure_star_partition :
  S.faces = (S.erasure A).faces ∪ S.star ((S.closure A).faces \ {∅}) :=
begin
  ext X,
  refine ⟨λ hX, _, _⟩,
  { by_cases ∀ ⦃W⦄, W ∈ A → disjoint W X,
    { exact or.inl ⟨hX, h⟩ },
    push_neg at h,
    obtain ⟨W, hW, hWX⟩ := h,
    right,
    obtain ⟨x, hxW, hxX⟩ := not_disjoint_iff.1 hWX,
    rw ←singleton_subset_iff at hxW hxX,
    exact ⟨hX, {x}, ⟨⟨S.down_closed hX hxX $ singleton_nonempty _, W, hW, hxW⟩,
      (singleton_nonempty x).ne_empty⟩, hxX⟩ },
  { rintro (hX | hX); exact hX.1 }
end

end geometry.simplicial_complex
