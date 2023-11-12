/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
import analysis.convex.normed
import analysis.convex.strict
import analysis.normed.order.basic
import analysis.normed_space.add_torsor
import analysis.normed_space.pointwise
import analysis.normed_space.affine_isometry

/-!
# Strictly convex spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines strictly convex spaces. A normed space is strictly convex if all closed balls are
strictly convex. This does **not** mean that the norm is strictly convex (in fact, it never is).

## Main definitions

`strict_convex_space`: a typeclass saying that a given normed space over a normed linear ordered
field (e.g., `ℝ` or `ℚ`) is strictly convex. The definition requires strict convexity of a closed
ball of positive radius with center at the origin; strict convexity of any other closed ball follows
from this assumption.

## Main results

In a strictly convex space, we prove

- `strict_convex_closed_ball`: a closed ball is strictly convex.
- `combo_mem_ball_of_ne`, `open_segment_subset_ball_of_ne`, `norm_combo_lt_of_ne`:
  a nontrivial convex combination of two points in a closed ball belong to the corresponding open
  ball;
- `norm_add_lt_of_not_same_ray`, `same_ray_iff_norm_add`, `dist_add_dist_eq_iff`:
  the triangle inequality `dist x y + dist y z ≤ dist x z` is a strict inequality unless `y` belongs
  to the segment `[x -[ℝ] z]`.
- `isometry.affine_isometry_of_strict_convex_space`: an isometry of `normed_add_torsor`s for real
  normed spaces, strictly convex in the case of the codomain, is an affine isometry.

We also provide several lemmas that can be used as alternative constructors for `strict_convex ℝ E`:

- `strict_convex_space.of_strict_convex_closed_unit_ball`: if `closed_ball (0 : E) 1` is strictly
  convex, then `E` is a strictly convex space;

- `strict_convex_space.of_norm_add`: if `‖x + y‖ = ‖x‖ + ‖y‖` implies `same_ray ℝ x y` for all
  nonzero `x y : E`, then `E` is a strictly convex space.

## Implementation notes

While the definition is formulated for any normed linear ordered field, most of the lemmas are
formulated only for the case `𝕜 = ℝ`.

## Tags

convex, strictly convex
-/

open set metric
open_locale convex pointwise

/-- A *strictly convex space* is a normed space where the closed balls are strictly convex. We only
require balls of positive radius with center at the origin to be strictly convex in the definition,
then prove that any closed ball is strictly convex in `strict_convex_closed_ball` below.

See also `strict_convex_space.of_strict_convex_closed_unit_ball`. -/
class strict_convex_space (𝕜 E : Type*) [normed_linear_ordered_field 𝕜] [normed_add_comm_group E]
  [normed_space 𝕜 E] : Prop :=
(strict_convex_closed_ball : ∀ r : ℝ, 0 < r → strict_convex 𝕜 (closed_ball (0 : E) r))

variables (𝕜 : Type*) {E : Type*} [normed_linear_ordered_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E]

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

/-- Strict convexity is equivalent to `‖a • x + b • y‖ < 1` for all `x` and `y` of norm at most `1`
and all strictly positive `a` and `b` such that `a + b = 1`. This lemma shows that it suffices to
check this for points of norm one and some `a`, `b` such that `a + b = 1`. -/
lemma strict_convex_space.of_norm_combo_lt_one
  (h : ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y → ∃ a b : ℝ, a + b = 1 ∧ ‖a • x + b • y‖ < 1) :
  strict_convex_space ℝ E :=
begin
  refine strict_convex_space.of_strict_convex_closed_unit_ball ℝ
    ((convex_closed_ball _ _).strict_convex' $ λ x hx y hy hne, _),
  rw [interior_closed_ball (0 : E) one_ne_zero, closed_ball_diff_ball, mem_sphere_zero_iff_norm]
    at hx hy,
  rcases h x y hx hy hne with ⟨a, b, hab, hlt⟩,
  use b,
  rwa [affine_map.line_map_apply_module, interior_closed_ball (0 : E) one_ne_zero,
    mem_ball_zero_iff, sub_eq_iff_eq_add.2 hab.symm]
end

lemma strict_convex_space.of_norm_combo_ne_one
  (h : ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y →
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ ‖a • x + b • y‖ ≠ 1) :
  strict_convex_space ℝ E :=
begin
  refine strict_convex_space.of_strict_convex_closed_unit_ball ℝ
    ((convex_closed_ball _ _).strict_convex _),
  simp only [interior_closed_ball _ one_ne_zero, closed_ball_diff_ball, set.pairwise,
    frontier_closed_ball _ one_ne_zero, mem_sphere_zero_iff_norm],
  intros x hx y hy hne,
  rcases h x y hx hy hne with ⟨a, b, ha, hb, hab, hne'⟩,
  exact ⟨_, ⟨a, b, ha, hb, hab, rfl⟩, mt mem_sphere_zero_iff_norm.1 hne'⟩
end

lemma strict_convex_space.of_norm_add_ne_two
  (h : ∀ ⦃x y : E⦄, ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y → ‖x + y‖ ≠ 2) :
  strict_convex_space ℝ E :=
begin
  refine strict_convex_space.of_norm_combo_ne_one
    (λ x y hx hy hne, ⟨1/2, 1/2, one_half_pos.le, one_half_pos.le, add_halves _, _⟩),
  rw [← smul_add, norm_smul, real.norm_of_nonneg one_half_pos.le, one_div,
    ← div_eq_inv_mul, ne.def, div_eq_one_iff_eq (two_ne_zero' ℝ)],
  exact h hx hy hne,
end

lemma strict_convex_space.of_pairwise_sphere_norm_ne_two
  (h : (sphere (0 : E) 1).pairwise $ λ x y, ‖x + y‖ ≠ 2) :
  strict_convex_space ℝ E :=
strict_convex_space.of_norm_add_ne_two $ λ x y hx hy,
  h (mem_sphere_zero_iff_norm.2 hx) (mem_sphere_zero_iff_norm.2 hy)

/-- If `‖x + y‖ = ‖x‖ + ‖y‖` implies that `x y : E` are in the same ray, then `E` is a strictly
convex space. See also a more -/
lemma strict_convex_space.of_norm_add
  (h : ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → ‖x + y‖ = 2 → same_ray ℝ x y) :
  strict_convex_space ℝ E :=
begin
  refine strict_convex_space.of_pairwise_sphere_norm_ne_two (λ x hx y hy, mt $ λ h₂, _),
  rw mem_sphere_zero_iff_norm at hx hy,
  exact (same_ray_iff_of_norm_eq (hx.trans hy.symm)).1 (h x y hx hy h₂)
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
lemma norm_combo_lt_of_ne (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (hne : x ≠ y) (ha : 0 < a) (hb : 0 < b)
  (hab : a + b = 1) : ‖a • x + b • y‖ < r :=
begin
  simp only [← mem_ball_zero_iff, ← mem_closed_ball_zero_iff] at hx hy ⊢,
  exact combo_mem_ball_of_ne hx hy hne ha hb hab
end

/-- In a strictly convex space, if `x` and `y` are not in the same ray, then `‖x + y‖ < ‖x‖ +
‖y‖`. -/
lemma norm_add_lt_of_not_same_ray (h : ¬same_ray ℝ x y) : ‖x + y‖ < ‖x‖ + ‖y‖ :=
begin
  simp only [same_ray_iff_inv_norm_smul_eq, not_or_distrib, ← ne.def] at h,
  rcases h with ⟨hx, hy, hne⟩,
  rw ← norm_pos_iff at hx hy,
  have hxy : 0 < ‖x‖ + ‖y‖ := add_pos hx hy,
  have := combo_mem_ball_of_ne (inv_norm_smul_mem_closed_unit_ball x)
    (inv_norm_smul_mem_closed_unit_ball y) hne (div_pos hx hxy) (div_pos hy hxy)
    (by rw [← add_div, div_self hxy.ne']),
  rwa [mem_ball_zero_iff, div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul,
    smul_inv_smul₀ hx.ne', smul_inv_smul₀ hy.ne', ← smul_add, norm_smul,
    real.norm_of_nonneg (inv_pos.2 hxy).le, ← div_eq_inv_mul, div_lt_one hxy] at this
end

lemma lt_norm_sub_of_not_same_ray (h : ¬same_ray ℝ x y) : ‖x‖ - ‖y‖ < ‖x - y‖ :=
begin
  nth_rewrite 0 ←sub_add_cancel x y at ⊢ h,
  exact sub_lt_iff_lt_add.2 (norm_add_lt_of_not_same_ray $ λ H', h $ H'.add_left same_ray.rfl),
end

lemma abs_lt_norm_sub_of_not_same_ray (h : ¬same_ray ℝ x y) : |‖x‖ - ‖y‖| < ‖x - y‖ :=
begin
  refine abs_sub_lt_iff.2 ⟨lt_norm_sub_of_not_same_ray h, _⟩,
  rw norm_sub_rev,
  exact lt_norm_sub_of_not_same_ray (mt same_ray.symm h),
end

/-- In a strictly convex space, two vectors `x`, `y` are in the same ray if and only if the triangle
inequality for `x` and `y` becomes an equality. -/
lemma same_ray_iff_norm_add : same_ray ℝ x y ↔ ‖x + y‖ = ‖x‖ + ‖y‖ :=
⟨same_ray.norm_add, λ h, not_not.1 $ λ h', (norm_add_lt_of_not_same_ray h').ne h⟩

/-- If `x` and `y` are two vectors in a strictly convex space have the same norm and the norm of
their sum is equal to the sum of their norms, then they are equal. -/
lemma eq_of_norm_eq_of_norm_add_eq (h₁ : ‖x‖ = ‖y‖) (h₂ : ‖x + y‖ = ‖x‖ + ‖y‖) : x = y :=
(same_ray_iff_norm_add.mpr h₂).eq_of_norm_eq h₁

/-- In a strictly convex space, two vectors `x`, `y` are not in the same ray if and only if the
triangle inequality for `x` and `y` is strict. -/
lemma not_same_ray_iff_norm_add_lt : ¬ same_ray ℝ x y ↔ ‖x + y‖ < ‖x‖ + ‖y‖ :=
same_ray_iff_norm_add.not.trans (norm_add_le _ _).lt_iff_ne.symm

lemma same_ray_iff_norm_sub : same_ray ℝ x y ↔ ‖x - y‖ = |‖x‖ - ‖y‖| :=
⟨same_ray.norm_sub, λ h, not_not.1 $ λ h', (abs_lt_norm_sub_of_not_same_ray h').ne' h⟩

lemma not_same_ray_iff_abs_lt_norm_sub : ¬ same_ray ℝ x y ↔ |‖x‖ - ‖y‖| < ‖x - y‖ :=
same_ray_iff_norm_sub.not.trans $ ne_comm.trans (abs_norm_sub_norm_le _ _).lt_iff_ne.symm

/-- In a strictly convex space, the triangle inequality turns into an equality if and only if the
middle point belongs to the segment joining two other points. -/
lemma dist_add_dist_eq_iff : dist x y + dist y z = dist x z ↔ y ∈ [x -[ℝ] z] :=
by simp only [mem_segment_iff_same_ray, same_ray_iff_norm_add, dist_eq_norm',
  sub_add_sub_cancel', eq_comm]

lemma norm_midpoint_lt_iff (h : ‖x‖ = ‖y‖) : ‖(1/2 : ℝ) • (x + y)‖ < ‖x‖ ↔ x ≠ y :=
by rw [norm_smul, real.norm_of_nonneg (one_div_nonneg.2 zero_le_two), ←inv_eq_one_div,
    ←div_eq_inv_mul, div_lt_iff (zero_lt_two' ℝ), mul_two, ←not_same_ray_iff_of_norm_eq h,
    not_same_ray_iff_norm_add_lt, h]

variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
variables {PF : Type*} {PE : Type*} [metric_space PF] [metric_space PE]
variables [normed_add_torsor F PF] [normed_add_torsor E PE]

include E

lemma eq_line_map_of_dist_eq_mul_of_dist_eq_mul {x y z : PE} (hxy : dist x y = r * dist x z)
  (hyz : dist y z = (1 - r) * dist x z) :
  y = affine_map.line_map x z r :=
begin
  have : y -ᵥ x ∈ [(0 : E) -[ℝ] z -ᵥ x],
  { rw [← dist_add_dist_eq_iff, dist_zero_left, dist_vsub_cancel_right, ← dist_eq_norm_vsub',
      ← dist_eq_norm_vsub', hxy, hyz, ← add_mul, add_sub_cancel'_right, one_mul] },
  rcases eq_or_ne x z with rfl|hne,
  { obtain rfl : y = x, by simpa,
    simp },
  { rw [← dist_ne_zero] at hne,
    rcases this with ⟨a, b, ha, hb, hab, H⟩,
    rw [smul_zero, zero_add] at H,
    have H' := congr_arg norm H,
    rw [norm_smul, real.norm_of_nonneg hb, ← dist_eq_norm_vsub', ← dist_eq_norm_vsub', hxy,
      mul_left_inj' hne] at H',
    rw [affine_map.line_map_apply, ← H', H, vsub_vadd] },
end

lemma eq_midpoint_of_dist_eq_half {x y z : PE} (hx : dist x y = dist x z / 2)
  (hy : dist y z = dist x z / 2) : y = midpoint ℝ x z :=
begin
  apply eq_line_map_of_dist_eq_mul_of_dist_eq_mul,
  { rwa [inv_of_eq_inv, ← div_eq_inv_mul] },
  { rwa [inv_of_eq_inv, ← one_div, sub_half, one_div, ← div_eq_inv_mul] }
end

namespace isometry

include F

/-- An isometry of `normed_add_torsor`s for real normed spaces, strictly convex in the case of
the codomain, is an affine isometry.  Unlike Mazur-Ulam, this does not require the isometry to
be surjective.  -/
noncomputable def affine_isometry_of_strict_convex_space {f : PF → PE} (hi : isometry f) :
  PF →ᵃⁱ[ℝ] PE :=
{ norm_map := λ x, by simp [affine_map.of_map_midpoint, ←dist_eq_norm_vsub E, hi.dist_eq],
  ..affine_map.of_map_midpoint f (λ x y, begin
    apply eq_midpoint_of_dist_eq_half,
    { rw [hi.dist_eq, hi.dist_eq, dist_left_midpoint, real.norm_of_nonneg zero_le_two,
        div_eq_inv_mul] },
    { rw [hi.dist_eq, hi.dist_eq, dist_midpoint_right, real.norm_of_nonneg zero_le_two,
        div_eq_inv_mul] },
  end) hi.continuous }

@[simp] lemma coe_affine_isometry_of_strict_convex_space {f : PF → PE} (hi : isometry f) :
  ⇑(hi.affine_isometry_of_strict_convex_space) = f :=
rfl

@[simp] lemma affine_isometry_of_strict_convex_space_apply {f : PF → PE} (hi : isometry f)
  (p : PF) :
  hi.affine_isometry_of_strict_convex_space p = f p :=
rfl

end isometry
