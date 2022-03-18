/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
import analysis.convex.strict
import analysis.convex.topology
import analysis.normed_space.ordered
import analysis.normed_space.pointwise

/-!
# Strictly convex spaces

This file defines strictly convex spaces. A normed space is strictly convex if all closed balls are
strictly convex. This does **not** mean that the norm is strictly convex (in fact, it never is).
-/

open set metric
open_locale convex pointwise

/-- A *strictly convex space* is a normed space where the closed balls are strictly convex. We only
require balls of positive radius with center at the origin to be strictly convex in the definition,
then prove that any closed ball is strictly convex in `strict_convex_closed_ball` below.

See also `strict_convex_space.of_strict_convex_closed_unit_ball`. -/
class strict_convex_space (𝕜 E : Type*) [normed_linear_ordered_field 𝕜] [normed_group E]
  [normed_space 𝕜 E] : Prop :=
(strict_convex_closed_ball : ∀ r : ℝ, 0 < r → strict_convex 𝕜 (closed_ball (0 : E) r))

variables (𝕜 : Type*) {E : Type*} [normed_linear_ordered_field 𝕜]
  [normed_group E] [normed_space 𝕜 E]

/-- A closed ball in a strictly convex space is strictly convex. -/
lemma strict_convex_closed_ball [strict_convex_space 𝕜 E] (x : E) (r : ℝ) :
  strict_convex 𝕜 (closed_ball x r) :=
begin
  cases le_or_lt r 0 with hr hr,
  { exact (subsingleton_closed_ball x hr).strict_convex },
  rw ← vadd_closed_ball_zero,
  exact (strict_convex_space.strict_convex_closed_ball r hr).vadd _,
end

variables [normed_space ℝ E]

/-- A real normed vector space is strictly convex provided that the unit ball is strictly convex. -/
lemma strict_convex_space.of_strict_convex_closed_unit_ball
  [linear_map.compatible_smul E E 𝕜 ℝ] (h : strict_convex 𝕜 (closed_ball (0 : E) 1)) :
  strict_convex_space 𝕜 E :=
⟨λ r hr, by simpa only [smul_closed_unit_ball_of_nonneg hr.le] using h.smul r⟩

/-- If `∥x + y∥ = ∥x∥ + ∥y∥` implies that `x y : E` are in the same ray, then `E` is a strictly
convex space. -/
lemma strict_convex_space.of_norm_add (h : ∀ x y : E, ∥x + y∥ = ∥x∥ + ∥y∥ → same_ray ℝ x y) :
  strict_convex_space ℝ E :=
begin
  refine strict_convex_space.of_strict_convex_closed_unit_ball ℝ (λ x hx y hy hne a b ha hb hab, _),
  have hx' := hx, have hy' := hy,
  rw [← closure_closed_ball, closure_eq_interior_union_frontier,
    frontier_closed_ball (0 : E) one_ne_zero] at hx hy,
  cases hx, { exact (convex_closed_ball _ _).combo_mem_interior_left hx hy' ha hb.le hab },
  cases hy, { exact (convex_closed_ball _ _).combo_mem_interior_right hx' hy ha.le hb hab },
  rw [interior_closed_ball (0 : E) one_ne_zero, mem_ball_zero_iff],
  have hx₁ : ∥x∥ = 1, from mem_sphere_zero_iff_norm.1 hx,
  have hy₁ : ∥y∥ = 1, from mem_sphere_zero_iff_norm.1 hy,
  have ha' : ∥a∥ = a, from real.norm_of_nonneg ha.le,
  have hb' : ∥b∥ = b, from real.norm_of_nonneg hb.le,
  calc ∥a • x + b • y∥ < ∥a • x∥ + ∥b • y∥ : (norm_add_le _ _).lt_of_ne (λ H, hne _)
  ... = 1 : by simpa only [norm_smul, hx₁, hy₁, mul_one, ha', hb'],
  simpa only [norm_smul, hx₁, hy₁, ha', hb', mul_one, smul_comm a, smul_right_inj ha.ne',
    smul_right_inj hb.ne'] using (h _ _ H).norm_smul_eq.symm
end

variables [strict_convex_space ℝ E] {x y z : E} {a b r : ℝ}

/-- If `x ≠ y` belong to the same closed ball, then a convex combination of `x` and `y` with
positive coefficients belongs to the corresponding open ball. -/
lemma combo_mem_ball_of_ne (hx : x ∈ closed_ball z r) (hy : y ∈ closed_ball z r) (hne : x ≠ y)
  (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a • x + b • y ∈ ball z r :=
begin
  rcases eq_or_ne r 0 with rfl|hr,
  { rw [closed_ball_zero, mem_singleton_iff] at hx hy,
    exact (hne (hx.trans hy.symm)).elim },
  { simp only [← interior_closed_ball _ hr] at hx hy ⊢,
    exact strict_convex_closed_ball ℝ z r hx hy hne ha hb hab }
end

/-- If `x ≠ y` belong to the same closed ball, then the open segment with endpoints `x` and `y` is
included in the corresponding open ball. -/
lemma open_segment_subset_ball_of_ne (hx : x ∈ closed_ball z r) (hy : y ∈ closed_ball z r)
  (hne : x ≠ y) : open_segment ℝ x y ⊆ ball z r :=
(open_segment_subset_iff _).2 $ λ a b, combo_mem_ball_of_ne hx hy hne

/-- If `x` and `y` are two distinct vectors of norm at most `r`, then a convex combination of `x`
and `y` with positive coefficients has norm strictly less than `r`. -/
lemma norm_combo_lt_of_ne (hx : ∥x∥ ≤ r) (hy : ∥y∥ ≤ r) (hne : x ≠ y) (ha : 0 < a) (hb : 0 < b)
  (hab : a + b = 1) : ∥a • x + b • y∥ < r :=
begin
  simp only [← mem_ball_zero_iff, ← mem_closed_ball_zero_iff] at hx hy ⊢,
  exact combo_mem_ball_of_ne hx hy hne ha hb hab
end

/-- In a strictly convex space, if `x` and `y` are not in the same ray, then `∥x + y∥ < ∥x∥ +
∥y∥`. -/
lemma norm_add_lt_of_not_same_ray (h : ¬same_ray ℝ x y) : ∥x + y∥ < ∥x∥ + ∥y∥ :=
begin
  simp only [same_ray_iff_inv_norm_smul_eq, not_or_distrib, ← ne.def] at h,
  rcases h with ⟨hx, hy, hne⟩,
  rw ← norm_pos_iff at hx hy,
  have hxy : 0 < ∥x∥ + ∥y∥ := add_pos hx hy,
  have := combo_mem_ball_of_ne (inv_norm_smul_mem_closed_unit_ball x)
    (inv_norm_smul_mem_closed_unit_ball y) hne (div_pos hx hxy) (div_pos hy hxy)
    (by rw [← add_div, div_self hxy.ne']),
  rwa [mem_ball_zero_iff, div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul,
    smul_inv_smul₀ hx.ne', smul_inv_smul₀ hy.ne', ← smul_add, norm_smul,
    real.norm_of_nonneg (inv_pos.2 hxy).le, ← div_eq_inv_mul, div_lt_one hxy] at this
end

/-- In a strictly convex space, two vectors `x`, `y` are in the same ray if and only if the triangle
inequality for `x` and `y` becomes an equality. -/
lemma same_ray_iff_norm_add : same_ray ℝ x y ↔ ∥x + y∥ = ∥x∥ + ∥y∥ :=
⟨same_ray.norm_add, λ h, not_not.1 $ λ h', (norm_add_lt_of_not_same_ray h').ne h⟩

/-- In a strictly convex space, the triangle inequality turns into an equality if and only if the
middle point belongs to the segment joining two other points. -/
lemma dist_add_dist_eq_iff : dist x y + dist y z = dist x z ↔ y ∈ [x -[ℝ] z] :=
by simp only [mem_segment_iff_same_ray, same_ray_iff_norm_add, dist_eq_norm',
  sub_add_sub_cancel', eq_comm]
