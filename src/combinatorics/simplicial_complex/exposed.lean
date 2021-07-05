/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.exposed

open_locale classical affine big_operators
open set
--TODO: Generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B C : set E}
  {X : finset E} {l : E →L[ℝ] ℝ}

namespace is_exposed

lemma is_exposed_empty : is_exposed A ∅ :=
λ ⟨x, hx⟩, by { exfalso, exact hx }

lemma mono (hC : is_exposed A C) (hBA : B ⊆ A) (hCB : C ⊆ B) :
  is_exposed B C :=
begin
  rintro ⟨w, hw⟩,
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩,
  refine ⟨l, subset.antisymm _ _⟩,
  rintro x hx,
  exact ⟨hCB hx, λ y hy, hx.2 y (hBA hy)⟩,
  rintro x hx,
  exact ⟨hBA hx.1, λ y hy, (hw.2 y hy).trans (hx.2 w (hCB hw))⟩,
end

/-
instance : bounded_lattice (set_of (is_exposed A)) :=
{ sup := λ ⟨B, hB⟩ ⟨C, hC⟩, ⟨(⋂ (D : set E) (hD : is_exposed A D) (hDB : B ⊆ D) (hCB : C ⊆ D), D),
    begin
      apply Inter,
      sorry
    end⟩,
  le := λ ⟨B, hB⟩ ⟨C, hC⟩, is_exposed C B,
  le_refl := λ ⟨B, hB⟩, refl B,
  le_trans := λ ⟨B, hB⟩ ⟨C, hC⟩ ⟨D, hD⟩ (hBC : is_exposed _ _) (hCD : is_exposed _ _), hCD.trans hBC,
  le_antisymm := λ ⟨B, hB⟩ ⟨C, hC⟩ (hCB : is_exposed _ _) hBC, hBC.antisymm hCB,
  le_sup_left := _,
  le_sup_right := _,
  sup_le := _,
  inf := λ ⟨B, hB⟩ ⟨C, hC⟩, ⟨B ∩ C, hB.inter hC⟩,
  inf_le_left := begin -- λ ⟨B, hB⟩ ⟨C, hC⟩, (refl B).inter
    rintro ⟨B, hB⟩ ⟨C, hC⟩,
    rintro ⟨x, hxB, hxC⟩,
    obtain ⟨l, rfl⟩ := hC ⟨x, hxC⟩,
    refine ⟨l, subset.antisymm _ _⟩,
    rintro y ⟨hyB, ⟨_, hy⟩⟩,
    exact ⟨hyB, λ z hz, hy z (hB.subset hz)⟩,
    rintro y ⟨hyB, hy⟩,
    exact ⟨hyB, (hB.subset hyB), λ z hz, (hxC.2 z hz).trans (hy x hxB)⟩,
  end,
  inf_le_right := λ ⟨B, hB⟩ ⟨C, hC⟩, begin
    simp *,
  end,
  le_inf := λ ⟨B, hB⟩ ⟨C, hC⟩ ⟨D, hD⟩ (hBC : is_exposed _ _) (hBD : is_exposed _ _), hBC.inter_left
    hBD.subset,
  top := ⟨A, refl A⟩,
  le_top := λ ⟨B, hB⟩, hB,
  bot := ⟨∅, is_exposed_empty⟩,
  bot_le := λ ⟨B, hB⟩, is_exposed_empty }-/

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
