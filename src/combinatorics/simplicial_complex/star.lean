/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.basic
import combinatorics.simplicial_complex.closure

/-!
# Star in a simplicial complex
-/

open set

variables {𝕜 E : Type*}

section ordered_ring
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {n : ℕ}
  {S : simplicial_complex 𝕜 E} {X Y : finset E} {A B : set (finset E)}

/-- The open star of a set of faces is the union of their surfaces. Note that the star is all of the
original complex as soon as A contains the empty set. -/
def simplicial_complex.star (S : simplicial_complex 𝕜 E) :
  set (finset E) → set (finset E) :=
λ A, {X | X ∈ S.faces ∧ ∃ {Y}, Y ∈ A ∧ Y ⊆ X}

lemma star_empty :
  S.star ∅ = ∅ :=
begin
  unfold simplicial_complex.star,
  simp,
end

lemma star_singleton_empty :
  S.star {∅} = S.faces :=
begin
  unfold simplicial_complex.star,
  simp,
end

lemma mem_star_singleton_iff :
  Y ∈ S.star {X} ↔ Y ∈ S.faces ∧ X ⊆ Y :=
begin
  unfold simplicial_complex.star,
  simp,
end

lemma mem_star_iff :
  X ∈ S.star A ↔ X ∈ S.faces ∩ ⋃ (Y ∈ A), {Z | Y ⊆ Z} :=
begin
  unfold simplicial_complex.star,
  simp,
end

lemma star_subset : S.star A ⊆ S.faces :=
  λ X hX, hX.1

lemma subset_star :
  S.faces ∩ A ⊆ S.star A :=
λ X hX, ⟨hX.1, X, hX.2, subset.refl X⟩

lemma star_mono (hAB : A ⊆ B) :
  S.star A ⊆ S.star B :=
λ X ⟨hX, Y, hY, hYX⟩, ⟨hX, Y, hAB hY, hYX⟩

lemma star_up_closed :
  X ∈ S.faces → Y ∈ S.star A → Y ⊆ X → X ∈ S.star A :=
λ hX ⟨hY, Z, hZ, hZY⟩ hYX, ⟨hX, Z, hZ, subset.trans hZY hYX⟩

lemma Union_star_eq_star :
  (⋃ (X ∈ A), S.star {X}) = S.star A :=
begin
  ext X,
  rw mem_bUnion_iff,
  split,
  { rintro ⟨Y', hY, hX, Y, (hYY' : Y = Y'), hYX⟩,
    subst hYY',
    exact ⟨hX, Y, hY, hYX⟩,
  },
  { rintro ⟨hX, Y, hY, hYX⟩,
    exact ⟨Y, hY, hX, Y, mem_singleton Y, hYX⟩,
  }
end

--Can maybe get rid of hX?
lemma star_singleton_eq_Inter_star_singleton (hX : X ∈ S.faces) :
  S.star {X} = ⋂ x ∈ X, S.star {{x}} :=
begin
  ext Y,
  split,
  { rintro ⟨hY, Z, (hZ : Z = X), hXY⟩,
    rw hZ at hXY,
    exact mem_bInter (λ x (hx : x ∈ X), ⟨hY, {x}, mem_singleton {x},
      finset.singleton_subset_iff.2 (hXY hx)⟩) },
  { rintro h,
    rw mem_star_singleton_iff,
    split,
    { simp only [mem_Inter] at h,
      sorry
    },
    rintro x hx,
    obtain ⟨hY, Z, (hZ : Z = {x}), hxY⟩ := mem_bInter_iff.1 h x hx,
    rw hZ at hxY,
    exact finset.singleton_subset_iff.1 hxY }
end

/--
The closed star of a complex S and a set A is the complex whose faces are in S and share a surface
with some face in A
-/
def simplicial_complex.Star (S : simplicial_complex 𝕜 E) (A : set (finset E)) :
  simplicial_complex 𝕜 E :=
simplicial_complex.of_subcomplex {X | ∃ {Y Z}, Y ∈ A ∧ Z ∈ S.faces ∧ X ⊆ Z ∧ Y ⊆ Z}
  (λ X ⟨_, Z, _, hZ, hXZ, _⟩, S.down_closed hZ hXZ)
  (λ X W ⟨Y, Z, hY, hZ, hXZ, hYZ⟩ hWX, ⟨Y, Z, hY, hZ, subset.trans hWX hXZ, hYZ⟩)

lemma Star_empty :
  (S.Star ∅).faces = ∅ :=
begin
  unfold simplicial_complex.Star,
  simp,
end

lemma Star_singleton_empty :
  S.Star {∅} = S :=
begin
  ext X,
  split,
  { rintro ⟨Y, Z, (hY : Y = ∅), hZ, hXZ, hYZ⟩,
    exact S.down_closed hZ hXZ,
  },
  { rintro hX,
    exact ⟨∅, X, rfl, hX, subset.refl _, empty_subset X⟩,
  }
end

lemma mem_Star_singleton_iff :
  Y ∈ (S.Star {X}).faces ↔ ∃ {Z}, Z ∈ S.faces ∧ Y ⊆ Z ∧ X ⊆ Z :=
begin
  unfold simplicial_complex.Star,
  simp,
end

/--
The closed star of a set is the closure of its open star.
-/
lemma Star_eq_closure_star :
  S.Star A = S.closure (S.star A) :=
begin
  ext X,
  split,
  { rintro ⟨Y, Z, hY, hZ, hXZ, hYZ⟩,
    exact ⟨S.down_closed hZ hXZ, Z, ⟨hZ, Y, hY, hYZ⟩, hXZ⟩,
  },
  { rintro ⟨hX, Z, ⟨hZ, Y, hY, hYZ⟩, hXZ⟩,
    exact ⟨Y, Z, hY, hZ, hXZ, hYZ⟩,
  }
end

lemma Star_subset :
  (S.Star A).faces ⊆ S.faces :=
λ X ⟨_, Z, _, hZ, hXZ, _⟩, S.down_closed hZ hXZ

lemma subset_Star :
  S.faces ∩ A ⊆ (S.Star A).faces :=
λ X ⟨hXS, hXA⟩, ⟨X, X, hXA, hXS, subset.refl X, subset.refl X⟩

lemma star_subset_Star :
  S.star A ⊆ (S.Star A).faces :=
λ X ⟨hX, Y, hY, hYX⟩, ⟨Y, X, hY, hX, subset.refl X, hYX⟩

lemma Star_mono (hAB : A ⊆ B) :
  (S.Star A).faces ⊆ (S.Star B).faces :=
begin
  rw [Star_eq_closure_star, Star_eq_closure_star],
  exact closure_faces_subset_of_subset (star_mono hAB),
end

lemma Star_facet_iff :
  X ∈ (S.Star A).facets ↔ X ∈ S.facets ∧ ∃ {Y}, Y ∈ A ∧ Y ⊆ X :=
begin
  split,
  { rintro ⟨⟨Y, Z, hY, hZ, hXZ, hYZ⟩, hXmax⟩,
    have := hXmax ⟨Y, Z, hY, hZ, subset.refl Z, hYZ⟩ hXZ,
    subst this,
    split,
    {   use hZ,
      rintro W hW hXW,
      exact hXmax (star_subset_Star ⟨hW, Y, hY, subset.trans hYZ hXW⟩) hXW,
    },
    { exact ⟨Y, hY, hYZ⟩, }
  },
  { rintro ⟨hX, Y, hY, hYX⟩,
    split,
    exact ⟨Y, X, hY, hX.1, subset.refl X, hYX⟩,
    rintro Z hZ,
    exact hX.2 (Star_subset hZ),
  }
end

lemma pure_Star_of_pure (hS : S.pure_of n) :
  (S.Star A).pure_of n :=
λ X hX, hS (Star_facet_iff.1 hX).1

end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜]

lemma Star_pureness_eq_pureness [finite_dimensional 𝕜 E] (hS : S.pure)
  (hSA : (S.Star A).faces.nonempty) :
  (S.Star A).pureness = S.pureness :=
begin
  obtain ⟨n, hS⟩ := hS,
  obtain ⟨X, hX⟩ := id hSA,
  rw [pureness_def' hSA (pure_Star_of_pure hS), pureness_def' (hSA.mono Star_subset) hS],
end
