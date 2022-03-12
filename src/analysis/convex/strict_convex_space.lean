/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
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

open metric
open_locale convex pointwise

/-- A *strictly convex space* is a normed space where the closed balls are strictly convex. We only
require balls of positive radius with center at the origin to be strictly convex in the definition,
then prove that any closed ball is strictly convex in `strict_convex_closed_ball` below.

See also `strict_convex_space.of_strict_convex_closed_unit_ball`. -/
class strict_convex_space (𝕜 E : Type*) [normed_linear_ordered_field 𝕜] [normed_group E]
  [normed_space 𝕜 E] : Prop :=
(strict_convex_closed_ball : ∀ r : ℝ, 0 < r → strict_convex 𝕜 (closed_ball (0 : E) r))

variables (𝕜 : Type*) {E : Type*} [normed_linear_ordered_field 𝕜]

variables [normed_group E] [normed_space 𝕜 E]

/-- A closed ball in a strictly convex space is strictly convex. -/
lemma strict_convex_closed_ball [strict_convex_space 𝕜 E] (x : E) (r : ℝ) :
  strict_convex 𝕜 (closed_ball x r) :=
begin
  cases le_or_lt r 0 with hr hr,
  { exact (subsingleton_closed_ball x hr).strict_convex },
  rw ←vadd_closed_ball_zero,
  exact (strict_convex_space.strict_convex_closed_ball r hr).vadd _,
end

variables [normed_space ℝ E]

/-- A real normed vector space is strictly convex provided that the unit ball is strictly convex. -/
lemma strict_convex_space.of_strict_convex_closed_unit_ball
  [linear_map.compatible_smul E E 𝕜 ℝ] (h : strict_convex 𝕜 (closed_ball (0 : E) 1)) :
  strict_convex_space 𝕜 E :=
⟨λ r hr, by simpa only [smul_closed_unit_ball_of_nonneg hr.le] using h.smul r⟩

lemma strict_convex_space.of_norm_add
  (h : ∀ x y : E, x ≠ 0 → y ≠ 0 → ∥x + y∥ = ∥x∥ + ∥y∥ → ∥x∥ • y = ∥y∥ • x) :
  strict_convex_space ℝ E :=
begin
  refine strict_convex_space.of_strict_convex_closed_unit_ball ℝ (λ x hx y hy hne a b ha hb hab, _),
  have hx' := hx, have hy' := hy,
  rw [←closure_closed_ball, closure_eq_interior_union_frontier,
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
  have : ∥a • x∥ • b • y = ∥b • y∥ • a • x,
    from h (a • x) (b • y) (smul_ne_zero.2 ⟨ha.ne', ne_of_mem_sphere hx one_ne_zero⟩)
      (smul_ne_zero.2 ⟨hb.ne', ne_of_mem_sphere hy one_ne_zero⟩) H,
  simpa only [norm_smul, hx₁, hy₁, ha', hb', mul_one, smul_comm a, smul_right_inj ha.ne',
    smul_right_inj hb.ne'] using this.symm
end

variables [strict_convex_space ℝ E] {x y z : E} {a b r : ℝ}

lemma norm_combo_lt_of_ne (hx : ∥x∥ ≤ r) (hy : ∥y∥ ≤ r) (hxy : x ≠ y) (ha : 0 < a) (hb : 0 < b)
  (hab : a + b = 1) : ∥a • x + b • y∥ < r :=
begin
  have hr : r ≠ 0,
  { rintro rfl,
    rw [norm_le_zero_iff] at hx hy,
    exact hxy (hx.trans hy.symm) },
  simp only [←mem_closed_ball_zero_iff, ←mem_ball_zero_iff, ←interior_closed_ball _ hr]
    at hx hy ⊢,
  exact strict_convex_closed_ball ℝ (0 : E) r hx hy hxy ha hb hab
end

/-- In a strictly convex space, if `x` and `y` do not have the same direction, then
`∥x + y∥ < ∥x∥ + ∥y∥`. See also `norm_add_lt_of_ne`. -/
lemma norm_add_lt_of_div_norm_ne (hx : x ≠ 0) (hy : y ≠ 0) (h : ∥x∥⁻¹ • x ≠ ∥y∥⁻¹ • y) :
  ∥x + y∥ < ∥x∥ + ∥y∥ :=
begin
  rw ←norm_pos_iff at hx hy,
  rw [←div_lt_one (add_pos hx hy)],
  simpa [interior_closed_ball _ one_ne_zero, smul_smul, div_eq_inv_mul,
    mul_inv_cancel_right₀ hx.ne', mul_inv_cancel_right₀ hy.ne', ←smul_add, norm_smul,
    real.norm_of_nonneg (add_pos hx hy).le]
    using strict_convex_iff_div.1 (strict_convex_closed_ball ℝ (0 : E) 1)
      (inv_norm_smul_mem_closed_unit_ball x) (inv_norm_smul_mem_closed_unit_ball y) h hx hy,
end

/-- In a strictly convex space, if `x` and `y` do not have the same direction, then
`∥x + y∥ < ∥x∥ + ∥y∥`. See also `norm_add_lt_of_div_norm_ne`. -/
lemma norm_add_lt_of_ne (h : ∥x∥ • y ≠ ∥y∥ • x) : ∥x + y∥ < ∥x∥ + ∥y∥ :=
begin
  have hx : x ≠ 0, { rintro rfl, simpa using h },
  have hy : y ≠ 0, { rintro rfl, simpa using h },
  refine norm_add_lt_of_div_norm_ne hx hy _,
  rw ←norm_ne_zero_iff at hx hy,
  rwa [ne.def, ←smul_right_inj hx, smul_inv_smul₀ hx, smul_comm, ←smul_right_inj hy,
    smul_inv_smul₀ hy, eq_comm]; apply_instance
end

/-- In a strictly convex space, `∥x + y∥ = ∥x∥ + ∥y∥` if and only if `x` and `y` are -/
lemma norm_add_eq_iff : ∥x + y∥ = ∥x∥ + ∥y∥ ↔ ∥x∥ • y = ∥y∥ • x :=
⟨not_imp_not.1 $ λ h, (norm_add_lt_of_ne h).ne, norm_add_eq_of_norm_smul_eq⟩

/-- In a strictly convex space, the triangle inequality turns into an equality if and only if the
middle point belongs to the segment joining two other points. -/
lemma dist_add_dist_eq_iff : dist x y + dist y z = dist x z ↔ y ∈ [x -[ℝ] z] :=
begin
  refine ⟨_, dist_add_dist_of_mem_segment⟩, intro h,
  simp only [dist_eq_norm, ←sub_add_sub_cancel x y z, eq_comm.trans norm_add_eq_iff] at h,
  rcases eq_or_ne x y with rfl|hx, { apply left_mem_segment },
  rcases eq_or_ne y z with rfl|hy, { apply right_mem_segment },
  rw [←sub_ne_zero, ←norm_pos_iff] at hx hy,
  rw [←mem_segment_translate ℝ (-y), add_left_neg, ←sub_eq_neg_add, ←sub_eq_neg_add],
  refine mem_segment_iff_div.2 ⟨∥y - z∥, ∥x - y∥, hy.le, hx.le, add_pos hy hx, _⟩,
  simp only [div_eq_inv_mul, mul_smul, ←h, ←smul_add, sub_add_sub_cancel', sub_self, smul_zero]
end
