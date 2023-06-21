/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import analysis.convex.between
import analysis.convex.strict_convex_space

/-!
# Betweenness in affine spaces for strictly convex spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves results about betweenness for points in an affine space for a strictly convex
space.

-/

variables {V P : Type*} [normed_add_comm_group V] [normed_space ℝ V] [pseudo_metric_space P]
variables [normed_add_torsor V P] [strict_convex_space ℝ V]

include V

lemma sbtw.dist_lt_max_dist (p : P) {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) :
  dist p₂ p < max (dist p₁ p) (dist p₃ p) :=
begin
  have hp₁p₃ : p₁ -ᵥ p ≠ p₃ -ᵥ p, { by simpa using h.left_ne_right },
  rw [sbtw, ←wbtw_vsub_const_iff p, wbtw, affine_segment_eq_segment,
      ←insert_endpoints_open_segment, set.mem_insert_iff, set.mem_insert_iff] at h,
  rcases h with ⟨h | h | h, hp₂p₁, hp₂p₃⟩,
  { rw vsub_left_cancel_iff at h, exact false.elim (hp₂p₁ h) },
  { rw vsub_left_cancel_iff at h, exact false.elim (hp₂p₃ h) },
  { rw [open_segment_eq_image, set.mem_image] at h,
    rcases h with ⟨r, ⟨hr0, hr1⟩, hr⟩,
    simp_rw [@dist_eq_norm_vsub V, ←hr],
    exact norm_combo_lt_of_ne (le_max_left _ _) (le_max_right _ _) hp₁p₃ (sub_pos.2 hr1) hr0
      (by abel) }
end

lemma wbtw.dist_le_max_dist (p : P) {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) :
  dist p₂ p ≤ max (dist p₁ p) (dist p₃ p) :=
begin
  by_cases hp₁ : p₂ = p₁, { simp [hp₁] },
  by_cases hp₃ : p₂ = p₃, { simp [hp₃] },
  have hs : sbtw ℝ p₁ p₂ p₃ := ⟨h, hp₁, hp₃⟩,
  exact (hs.dist_lt_max_dist _).le
end

/-- Given three collinear points, two (not equal) with distance `r` from `p` and one with
distance at most `r` from `p`, the third point is weakly between the other two points. -/
lemma collinear.wbtw_of_dist_eq_of_dist_le {p p₁ p₂ p₃ : P} {r : ℝ}
  (h : collinear ℝ ({p₁, p₂, p₃} : set P)) (hp₁ : dist p₁ p = r) (hp₂ : dist p₂ p ≤ r)
  (hp₃ : dist p₃ p = r) (hp₁p₃ : p₁ ≠ p₃) : wbtw ℝ p₁ p₂ p₃ :=
begin
  rcases h.wbtw_or_wbtw_or_wbtw with hw | hw | hw,
  { exact hw },
  { by_cases hp₃p₂ : p₃ = p₂, { simp [hp₃p₂] },
    have hs : sbtw ℝ p₂ p₃ p₁ := ⟨hw, hp₃p₂, hp₁p₃.symm⟩,
    have hs' := hs.dist_lt_max_dist p,
    rw [hp₁, hp₃, lt_max_iff, lt_self_iff_false, or_false] at hs',
    exact false.elim (hp₂.not_lt hs') },
  { by_cases hp₁p₂ : p₁ = p₂, { simp [hp₁p₂] },
    have hs : sbtw ℝ p₃ p₁ p₂ := ⟨hw, hp₁p₃, hp₁p₂⟩,
    have hs' := hs.dist_lt_max_dist p,
    rw [hp₁, hp₃, lt_max_iff, lt_self_iff_false, false_or] at hs',
    exact false.elim (hp₂.not_lt hs') }
end

/-- Given three collinear points, two (not equal) with distance `r` from `p` and one with
distance less than `r` from `p`, the third point is strictly between the other two points. -/
lemma collinear.sbtw_of_dist_eq_of_dist_lt {p p₁ p₂ p₃ : P} {r : ℝ}
  (h : collinear ℝ ({p₁, p₂, p₃} : set P)) (hp₁ : dist p₁ p = r) (hp₂ : dist p₂ p < r)
  (hp₃ : dist p₃ p = r) (hp₁p₃ : p₁ ≠ p₃) : sbtw ℝ p₁ p₂ p₃ :=
begin
  refine ⟨h.wbtw_of_dist_eq_of_dist_le hp₁ hp₂.le hp₃ hp₁p₃, _, _⟩,
  { rintro rfl, exact hp₂.ne hp₁ },
  { rintro rfl, exact hp₂.ne hp₃ }
end
