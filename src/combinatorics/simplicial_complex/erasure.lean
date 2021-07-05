/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.link

namespace affine
open set
variables {E : Type*} [normed_group E] [normed_space ℝ E] {S : simplicial_complex E}
  {A : set (finset E)}

/--
The erasure of a simplicial complex S and a set A is the subcomplex obtained after removing all
faces having a vertex in A.
-/
def simplicial_complex.erasure (S : simplicial_complex E) (A : set (finset E)) :
  simplicial_complex E :=
simplicial_complex.of_surcomplex
  {X | X ∈ S.faces ∧ ∀ {W}, W ∈ A → disjoint W X}
  (λ X hX, hX.1)
  (λ X Y ⟨hX, hXA⟩ hYX, ⟨S.down_closed hX hYX, λ Z hZ, finset.disjoint_of_subset_right hYX (hXA hZ)⟩)
/-Previous def
def simplicial_complex.erasure (S : simplicial_complex E) (A : set (finset E)) :
  simplicial_complex E :=
simplicial_complex.of_surcomplex
  {X | X ∈ S.faces ∧ ∀ {Y}, Y ∈ A → disjoint X Y}
  (λ X hX, hX.1)
  (λ X Y ⟨hX, hXA⟩ hYX, ⟨S.down_closed hX hYX, λ Z hZ, finset.disjoint_of_subset_left hYX (hXA hZ)⟩)-/

lemma erasure_subset :
  (S.erasure A).faces ⊆ S.faces :=
λ X hX, hX.1

lemma link_eq_erasure_Star :
  S.link A = (S.Star A).erasure A :=
begin
  ext X,
  split,
  { rintro ⟨hXdisj, hXStar⟩,
    exact ⟨hXStar, (λ W, hXdisj)⟩ },
  { rintro ⟨hXStar, hXdisj⟩,
    exact ⟨(λ W, hXdisj), hXStar⟩ }
end

lemma erasure_and_closure_star_partition :
  S.faces = (S.erasure A).faces ∪ S.star ((S.closure A).faces \ {∅}) :=
begin
  ext X,
  split,
  { rintro hX,
    by_cases (∀ {W}, W ∈ A → disjoint W X),
    { left,
      exact ⟨hX, (λ W, h)⟩ },
    { right,
      push_neg at h,
      obtain ⟨W, hW, hWX⟩ := h,
      rw finset.disjoint_iff_inter_eq_empty at hWX,
      change W ∩ X ≠ ∅ at hWX,
      obtain ⟨x, hx⟩ := finset.nonempty_iff_ne_empty.2 hWX,
      rw ← finset.singleton_subset_iff at hx,
      use [hX, {x}],
      split,
      split,
      exact ⟨S.down_closed hX (subset.trans hx (finset.inter_subset_right W X)), W, hW,
        finset.subset.trans hx (finset.inter_subset_left W X)⟩,
      exact finset.nonempty_iff_ne_empty.1 (finset.singleton_nonempty x),
      exact finset.subset.trans hx (finset.inter_subset_right W X) }},
  { rintro (hX | hX);
    exact hX.1 }
end

end affine
