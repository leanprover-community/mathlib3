/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.pure

/-!
# Closure of a simplicial complex
-/

open_locale classical affine big_operators
open set

namespace affine

variables {𝕜 E : Type*} [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {m n : ℕ}
  {S : simplicial_complex 𝕜 E} {x : E} {X Y : finset E} {A B : set (finset E)}

/-- The closure of a set of faces is the set of their subfaces. -/
def simplicial_complex.closure (S : simplicial_complex 𝕜 E) (A : set (finset E)) :
  simplicial_complex 𝕜 E :=
simplicial_complex.of_subcomplex
  {X | X ∈ S.faces ∧ ∃ {X'}, X' ∈ A ∧ X ⊆ X'}
  (λ X ⟨hX, _⟩, hX)
  (λ X Y ⟨hX, X', hX', hXX'⟩ hYX, ⟨S.down_closed hX hYX, X', hX', subset.trans hYX hXX'⟩)

lemma closure_subset :
  (S.closure A).faces ⊆ S.faces :=
λ X ⟨hX, _⟩, hX

--Homonymy problem
lemma closure_empty :
  (S.closure ∅).faces = ∅ :=
begin
  unfold simplicial_complex.closure,
  simp,
end

lemma closure_singleton_empty (hS : S.faces.nonempty) :
  (S.closure {∅}).faces = {∅} :=
begin
  ext X,
  split,
  { rintro ⟨hX, X', (hX' : X' = ∅), hXX'⟩,
    rw hX' at hXX',
    exact finset.subset_empty.1 hXX' },
  { rintro (hX : X = ∅),
    rw hX,
    obtain ⟨Y, hY⟩ := hS,
    exact ⟨S.down_closed hY (empty_subset Y), ∅, mem_singleton ∅, subset.refl ∅⟩ }
end

--Homonymy problem
lemma closure_singleton (hx : {x} ∈ S.faces) :
  (S.closure {{x}}).faces = {∅, {x}} :=
begin
  ext Y,
  split,
  { rintro ⟨hY, Z, (hZ : Z = {x}), hYZ⟩,
    rw hZ at hYZ,
    simp only [mem_singleton_iff, mem_insert_iff],
    rwa ← finset.subset_singleton_iff },
  { have hxS : {x} ∈ (S.closure {{x}}).faces := ⟨hx, {x}, rfl, finset.subset.refl {x}⟩,
    simp only [mem_singleton_iff, mem_insert_iff],
    rintro (rfl | rfl),
    { exact empty_mem_faces_of_nonempty (nonempty_of_mem hxS) },
    { assumption } }
end

lemma mem_closure_singleton_iff :
  Y ∈ (S.closure {X}).faces ↔ Y ∈ S.faces ∧ Y ⊆ X :=
begin
  split,
  { rintro ⟨hY, Z, (hZ : Z = X), hYZ⟩,
    rw hZ at hYZ,
    exact ⟨hY, hYZ⟩ },
  { rintro ⟨hY, hYX⟩,
    exact ⟨hY, X, rfl, hYX⟩ }
end

--Homonymy problem
lemma faces_subset_closure :
  S.faces ∩ A ⊆ (S.closure A).faces :=
λ X hX, ⟨hX.1, X, hX.2, subset.refl _⟩

lemma closure_faces_subset_of_subset (hAB : A ⊆ B) :
  (S.closure A).faces ⊆ (S.closure B).faces :=
λ X ⟨hX, Y, hY, hXY⟩, ⟨hX, Y, hAB hY, hXY⟩

lemma closure_facets_eq (hA : A ⊆ S.faces) (hAtop : ∀ ⦃X Y⦄, X ∈ A → Y ∈ A → X ⊆ Y → X = Y) :
  (S.closure A).facets = A :=
begin
  ext X,
  split,
  { rintro ⟨⟨hX, Y, hY, hXY⟩, hXmax⟩,
    rw hXmax ⟨hA hY, Y, hY, finset.subset.refl _⟩ hXY,
    exact hY },
  { rintro hX,
    use ⟨hA hX, X, hX, finset.subset.refl _⟩,
    rintro Y ⟨hY, Z, hZ, hYZ⟩ hXY,
    have hXZ := hAtop hX hZ (subset.trans hXY hYZ),
    rw ←hXZ at hYZ,
    exact finset.subset.antisymm hXY hYZ }
end

lemma pure_closure_of_pure (hS : S.pure_of n)
  (hA : ∀ {W}, W ∈ A → ∃ {X}, X ∈ A ∧ X ∈ S.faces ∧ (X : finset E).card = m) :
  (S.closure A).pure_of m :=
begin
  sorry
end

end affine
