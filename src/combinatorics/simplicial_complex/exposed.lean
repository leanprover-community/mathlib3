/-
Copyright (c) 2021 Yaël Dillies, thavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, thavik Mehta
-/
import analysis.convex.exposed
import analysis.normed_space.hahn_banach.separation
import combinatorics.simplicial_complex.extreme

/-!
# Exposed sets
-/

open_locale affine big_operators classical
open set
--TODO: Generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {s t C : set E}
  {X : finset E} {l : E →L[ℝ] ℝ}

namespace is_exposed

lemma subset_frontier (hst : is_exposed ℝ s t) (hts : ¬ s ⊆ t) : t ⊆ frontier s :=
hst.is_extreme.subset_frontier hts

lemma span_lt (hst : is_exposed ℝ s t) (hts : ¬ s ⊆ t) : affine_span ℝ t < affine_span ℝ s :=
begin
  apply (affine_span_mono _ hst.subset).lt_of_ne,
  rintro h,
  sorry
end

end is_exposed

/-lemma is_exposed.dim_lt (hst : is_exposed s t) (hts : ¬ s ⊆ t) :
  (affine_span ℝ t).rank < (affine_span ℝ s).rank :=
begin

end-/

lemma mem_exposed_set_iff_mem_frontier (hs₁ : convex ℝ s) (hs₂ : (interior s).nonempty) :
  (∃ t : set E, is_exposed ℝ s t ∧ ¬ s ⊆ t ∧ x ∈ t) ↔ x ∈ s ∧ x ∈ frontier s :=
begin
  use λ ⟨t, hst, hts, hxt⟩, ⟨hst.subset hxt, hst.subset_frontier hts hxt⟩,
  rintro ⟨hxA, hxfA⟩,
  obtain ⟨y, hyA⟩ := id hs₂,
  obtain ⟨l, hl⟩ := geometric_hahn_banach_open_point (convex.interior hs₁) is_open_interior hxfA.2,
  refine ⟨{x ∈ s | ∀ y ∈ s, l y ≤ l x}, λ _, ⟨l, rfl⟩, λ h,
    not_le.2 (hl y hyA) ((h (interior_subset hyA)).2 x hxA), hxA, λ z hzA, _⟩,
  suffices h : l '' closure (interior s) ⊆ closure (Iio (l x)),
  { rw [closure_Iio, ←closure_eq_closure_interior hs₁ hs₂] at h,
    exact h ⟨z, subset_closure hzA, rfl⟩ },
  refine subset.trans (image_closure_subset_closure_image l.continuous) (closure_mono _),
  rintro _ ⟨w, hw, rfl⟩,
  exact hl w hw,
end

lemma mem_extreme_set_iff_mem_frontier (hs₁ : convex ℝ s) (hs₂ : (interior s).nonempty) :
  (∃ t : set E, is_extreme ℝ s t ∧ ¬ s ⊆ t ∧ x ∈ t) ↔ x ∈ s ∧ x ∈ frontier s :=
begin
  use λ ⟨t, hst, hts, hxt⟩, ⟨hst.1 hxt, hst.subset_frontier hts hxt⟩,
  rintro h,
  obtain ⟨t, hst, hts, hxt⟩ := (mem_exposed_set_iff_mem_frontier hs₁ hs₂).2 h,
  exact ⟨t, hst.is_extreme, hts, hxt⟩,
end

/-! # Harder stuff -/

lemma closed_extreme_points [finite_dimensional ℝ E] (hE : finite_dimensional.finrank ℝ E = 2)
  (hs₁ : convex ℝ s) (hs₂ : is_closed s) :
  is_closed (s.extreme_points ℝ) :=
begin
  sorry
end

--theorem of S. Straszewicz proved in 1935
lemma extreme_points_subset_closure_exposed_points (hs₁ : convex ℝ s) (hs₂ : is_closed s) :
  s.extreme_points ℝ ⊆ closure (s.exposed_points ℝ) :=
begin
  sorry
end
