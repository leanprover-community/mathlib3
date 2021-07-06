/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.exposed
import combinatorics.simplicial_complex.extreme

open_locale classical affine big_operators
open set
--TODO: Generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B C : set E}
  {X : finset E} {l : E →L[ℝ] ℝ}

namespace is_exposed

lemma subset_frontier (hAB : is_exposed A B) (hBA : ¬ A ⊆ B) :
  B ⊆ frontier A :=
hAB.is_extreme.subset_frontier hBA

lemma span_lt (hAB : is_exposed A B) (hBA : ¬ A ⊆ B) :
  affine_span ℝ B < affine_span ℝ A :=
begin
  apply (affine_span_mono _ hAB.subset).lt_of_ne,
  rintro h,
  sorry
end

end is_exposed

/-lemma is_exposed.dim_lt (hAB : is_exposed A B) (hBA : ¬ A ⊆ B) :
  (affine_span ℝ B).rank < (affine_span ℝ A).rank :=
begin

end-/

lemma mem_exposed_set_iff_mem_frontier (hA₁ : convex A) (hA₂ : (interior A).nonempty) :
  (∃ B : set E, is_exposed A B ∧ ¬A ⊆ B ∧ x ∈ B) ↔ x ∈ A ∧ x ∈ frontier A :=
begin
  use λ ⟨B, hAB, hBA, hxB⟩, ⟨hAB.subset hxB, hAB.subset_frontier hBA hxB⟩,
  rintro ⟨hxA, hxfA⟩,
  obtain ⟨y, hyA⟩ := id hA₂,
  obtain ⟨l, hl⟩ := geometric_hahn_banach_open_point (convex.interior hA₁) is_open_interior hxfA.2,
  refine ⟨{x ∈ A | ∀ y ∈ A, l y ≤ l x}, λ _, ⟨l, rfl⟩, λ h,
    not_le.2 (hl y hyA) ((h (interior_subset hyA)).2 x hxA), hxA, λ z hzA, _⟩,
  suffices h : l '' closure (interior A) ⊆ closure (Iio (l x)),
  { rw [closure_Iio, ←closure_eq_closure_interior hA₁ hA₂] at h,
    exact h ⟨z, subset_closure hzA, rfl⟩ },
  refine subset.trans (image_closure_subset_closure_image l.continuous) (closure_mono _),
  rintro _ ⟨w, hw, rfl⟩,
  exact hl w hw,
end

lemma mem_extreme_set_iff_mem_frontier (hA₁ : convex A) (hA₂ : (interior A).nonempty) :
  (∃ B : set E, is_extreme A B ∧ ¬A ⊆ B ∧ x ∈ B) ↔ x ∈ A ∧ x ∈ frontier A :=
begin
  use λ ⟨B, hAB, hBA, hxB⟩, ⟨hAB.1 hxB, hAB.subset_frontier hBA hxB⟩,
  rintro h,
  obtain ⟨B, hAB, hBA, hxB⟩ := (mem_exposed_set_iff_mem_frontier hA₁ hA₂).2 h,
  exact ⟨B, hAB.is_extreme, hBA, hxB⟩,
end

/-! # Harder stuff -/

/-- Eidelheit's Theorem -/
theorem eq_Inter_halfspaces (hA₁ : convex A) (hA₂ : is_closed A) :
  A = ⋂ (l : E →L[ℝ] ℝ), {x | ∃ y ∈ A, l x ≤ l y} :=
begin
  ext,
  simp only [mem_Inter],
  use λ hx l, ⟨x, hx, le_rfl⟩,
  rintro hx,
  by_contra,
  obtain ⟨l, s, hlA, hl⟩ := geometric_hahn_banach_closed_point hA₁ hA₂ h,
  obtain ⟨y, hy, hxy⟩ := hx l,
  linarith [hlA y hy],
end

lemma closed_extreme_points [finite_dimensional ℝ E] (hE : finite_dimensional.finrank ℝ E = 2)
(hA₁ : convex A) (hA₂ : is_closed A) :
  is_closed A.extreme_points :=
begin
  sorry
end

--theorem of S. Straszewicz proved in 1935
lemma limit_exposed_points_of_extreme (hA₁ : convex A) (hA₂ : is_closed A) :
  A.extreme_points ⊆ closure (A.exposed_points) :=
begin
  sorry
end
