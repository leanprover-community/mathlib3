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

We also provide several lemmas that can be used as alternative constructors for `strict_convex ℝ E`:

- `strict_convex_space.of_strict_convex_closed_unit_ball`: if `closed_ball (0 : E) 1` is strictly
  convex, then `E` is a strictly convex space;

- `strict_convex_space.of_norm_add`: if `∥x + y∥ = ∥x∥ + ∥y∥` implies `same_ray ℝ x y` for all
  `x y : E`, then `E` is a strictly convex space.

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
  cases hx, { exact (convex_closed_ball _ _).combo_interior_self_mem_interior hx hy' ha hb.le hab },
  cases hy, { exact (convex_closed_ball _ _).combo_self_interior_mem_interior hx' hy ha.le hb hab },
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

lemma strict_convex_space.of_norm_add_lt_aux {a b c d : ℝ} (ha : 0 < a) (hab : a + b = 1)
  (hc : 0 < c) (hd : 0 < d) (hcd : c + d = 1) (hca : c ≤ a) {x y : E} (hy : ∥y∥ ≤ 1)
  (hxy : ∥a • x + b • y∥ < 1) :
  ∥c • x + d • y∥ < 1 :=
begin
  have hbd : b ≤ d,
  { refine le_of_add_le_add_left (hab.trans_le _),
    rw ←hcd,
    exact add_le_add_right hca _ },
  have h₁ : 0 < c / a := div_pos hc ha,
  have h₂ : 0 ≤ d - c / a * b,
  { rw [sub_nonneg, mul_comm_div, ←le_div_iff' hc],
    exact div_le_div hd.le hbd hc hca },
  calc ∥c • x + d • y∥ = ∥(c / a) • (a • x + b • y) + (d - c / a * b) • y∥
        : by rw [smul_add, ←mul_smul, ←mul_smul, div_mul_cancel _ ha.ne', sub_smul,
            add_add_sub_cancel]
    ... ≤ ∥(c / a) • (a • x + b • y)∥ + ∥(d - c / a * b) • y∥ : norm_add_le _ _
    ... = c / a * ∥a • x + b • y∥ + (d - c / a * b) * ∥y∥
        : by rw [norm_smul_of_nonneg h₁.le, norm_smul_of_nonneg h₂]
    ... < c / a * 1 + (d - c / a * b) * 1
        : add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hxy h₁) (mul_le_mul_of_nonneg_left hy h₂)
    ... = 1 : begin
      nth_rewrite 0 ←hab,
      rw [mul_add, div_mul_cancel _ ha.ne', mul_one, add_add_sub_cancel, hcd],
    end,
end

/-- Strict convexity is equivalent to `∥a • x + b • y∥ < 1` for all `x` and `y` of norm at most `1`
and all strictly positive `a` and `b` such that `a + b = 1`. This shows that we only need to check
it for fixed `a` and `b`. -/
lemma strict_convex_space.of_norm_add_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
  (h : ∀ x y : E, ∥x∥ ≤ 1 → ∥y∥ ≤ 1 → x ≠ y → ∥a • x + b • y∥ < 1) :
  strict_convex_space ℝ E :=
begin
  refine strict_convex_space.of_strict_convex_closed_unit_ball _ (λ x hx y hy hxy c d hc hd hcd, _),
  rw [interior_closed_ball (0 : E) one_ne_zero, mem_ball_zero_iff],
  rw mem_closed_ball_zero_iff at hx hy,
  obtain hca | hac := le_total c a,
  { exact strict_convex_space.of_norm_add_lt_aux ha hab hc hd hcd hca hy (h _ _ hx hy hxy) },
  rw add_comm at ⊢ hab hcd,
  refine strict_convex_space.of_norm_add_lt_aux hb hab hd hc hcd _ hx _,
  { refine le_of_add_le_add_right (hcd.trans_le _),
    rw ←hab,
    exact add_le_add_left hac _ },
  { rw add_comm,
    exact h _ _ hx hy hxy }
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

lemma lt_norm_sub_of_not_same_ray (h : ¬same_ray ℝ x y) : ∥x∥ - ∥y∥ < ∥x - y∥ :=
begin
  nth_rewrite 0 ←sub_add_cancel x y at ⊢ h,
  exact sub_lt_iff_lt_add.2 (norm_add_lt_of_not_same_ray $ λ H', h $ H'.add_left same_ray.rfl),
end

lemma abs_lt_norm_sub_of_not_same_ray (h : ¬same_ray ℝ x y) : |∥x∥ - ∥y∥| < ∥x - y∥ :=
begin
  refine abs_sub_lt_iff.2 ⟨lt_norm_sub_of_not_same_ray h, _⟩,
  rw norm_sub_rev,
  exact lt_norm_sub_of_not_same_ray (mt same_ray.symm h),
end

/-- In a strictly convex space, two vectors `x`, `y` are in the same ray if and only if the triangle
inequality for `x` and `y` becomes an equality. -/
lemma same_ray_iff_norm_add : same_ray ℝ x y ↔ ∥x + y∥ = ∥x∥ + ∥y∥ :=
⟨same_ray.norm_add, λ h, not_not.1 $ λ h', (norm_add_lt_of_not_same_ray h').ne h⟩

/-- In a strictly convex space, two vectors `x`, `y` are not in the same ray if and only if the
triangle inequality for `x` and `y` is strict. -/
lemma not_same_ray_iff_norm_add_lt : ¬ same_ray ℝ x y ↔ ∥x + y∥ < ∥x∥ + ∥y∥ :=
same_ray_iff_norm_add.not.trans (norm_add_le _ _).lt_iff_ne.symm

lemma same_ray_iff_norm_sub : same_ray ℝ x y ↔ ∥x - y∥ = |∥x∥ - ∥y∥| :=
⟨same_ray.norm_sub, λ h, not_not.1 $ λ h', (abs_lt_norm_sub_of_not_same_ray h').ne' h⟩

lemma not_same_ray_iff_abs_lt_norm_sub : ¬ same_ray ℝ x y ↔ |∥x∥ - ∥y∥| < ∥x - y∥ :=
same_ray_iff_norm_sub.not.trans $ ne_comm.trans (abs_norm_sub_norm_le _ _).lt_iff_ne.symm

/-- In a strictly convex space, the triangle inequality turns into an equality if and only if the
middle point belongs to the segment joining two other points. -/
lemma dist_add_dist_eq_iff : dist x y + dist y z = dist x z ↔ y ∈ [x -[ℝ] z] :=
by simp only [mem_segment_iff_same_ray, same_ray_iff_norm_add, dist_eq_norm',
  sub_add_sub_cancel', eq_comm]

lemma norm_midpoint_lt_iff (h : ∥x∥ = ∥y∥) : ∥(1/2 : ℝ) • (x + y)∥ < ∥x∥ ↔ x ≠ y :=
by rw [norm_smul, real.norm_of_nonneg (one_div_nonneg.2 zero_le_two), ←inv_eq_one_div,
    ←div_eq_inv_mul, div_lt_iff (@zero_lt_two ℝ _ _), mul_two, ←not_same_ray_iff_of_norm_eq h,
    not_same_ray_iff_norm_add_lt, h]

namespace isometry

variables {F : Type*} [normed_group F] [normed_space ℝ F]

lemma map_neg_of_map_zero {f : F → E} (hi : isometry f) (h0 : f 0 = 0) (x : F) :
  f (-x) = -(f x) :=
begin
  have hn : ∥f (-x)∥ = ∥-(f x)∥,
  { rw [hi.norm_map_of_map_zero h0, norm_neg, norm_neg, hi.norm_map_of_map_zero h0] },
  rw [←same_ray_iff_of_norm_eq hn, same_ray_iff_norm_add, ←sub_eq_add_neg, ←dist_eq_norm,
      hi.dist_eq, dist_eq_norm, hi.norm_map_of_map_zero h0, norm_neg, norm_neg,
      hi.norm_map_of_map_zero h0, sub_eq_add_neg, ←neg_add, norm_neg],
  exact (same_ray.refl x).norm_add
end

lemma map_smul_nonneg_of_map_zero {f : F → E} (hi : isometry f) (h0 : f 0 = 0) {r : ℝ}
  (hr : 0 ≤ r) (x : F) :
  f (r • x) = r • f x :=
begin
  have hn : ∥f (r • x)∥ = ∥r • f x∥,
  { rw [hi.norm_map_of_map_zero h0, norm_smul, norm_smul,
        hi.norm_map_of_map_zero h0] },
  rw ←same_ray_iff_of_norm_eq hn,
  refine same_ray.nonneg_smul_right _ hr,
  rw [same_ray_iff_norm_add, ←neg_neg (f x), ←sub_eq_add_neg, ←hi.map_neg_of_map_zero h0,
      ←dist_eq_norm, hi.dist_eq, dist_eq_norm, sub_neg_eq_add, norm_neg,
      hi.norm_map_of_map_zero h0, hi.norm_map_of_map_zero h0, norm_neg],
  exact (same_ray_nonneg_smul_left x hr).norm_add
end

lemma map_smul_of_map_zero {f : F → E} (hi : isometry f) (h0 : f 0 = 0) (r : ℝ) (x : F) :
  f (r • x) = r • f x :=
begin
  rcases le_or_lt 0 r with (h|h),
  { exact hi.map_smul_nonneg_of_map_zero h0 h x },
  { rw [←neg_neg r, neg_smul, hi.map_neg_of_map_zero h0, neg_smul (-r)],
    congr,
    rw ←neg_pos at h,
    exact hi.map_smul_nonneg_of_map_zero h0 h.le x }
end

lemma map_add_eq_smul_sub_map_sub {f : F → E} (hi : isometry f) (x y : F) :
  f (x + y) = (2 : ℕ) • f x - f (x - y) :=
begin
  set g : F → E := λ v, f (x + v) - f x with hg,
  have hg0 : g 0 = 0, { rw hg, simp },
  have hfg : ∀ v, f (x + v) = g v + f x, { simp [hg] },
  have hig : isometry g,
  { intros u v, simp [hg, hi.edist_eq] },
  rw [sub_eq_add_neg x, hfg, hfg, hig.map_neg_of_map_zero hg0],
  abel
end

lemma map_add_eq_smul_sub_map_sub_rev {f : F → E} (hi : isometry f) (x y : F) :
  f (x + y) = (2 : ℕ) • f y - f (y - x) :=
by rw [add_comm, hi.map_add_eq_smul_sub_map_sub]

lemma map_add_of_map_zero {f : F → E} (hi : isometry f) (h0 : f 0 = 0) (x y : F):
  f (x + y) = f x + f y :=
calc f (x + y) = (2⁻¹ : ℝ) • (2 : ℝ) • f (x + y) : by simp
     ...       = (2⁻¹ : ℝ) • (f (x + y) + f (x + y)) : by simp [two_smul]
     ...       = (2⁻¹ : ℝ) • ((2 : ℕ) • f x - f (x - y) + ((2 : ℕ) • f y - f (y - x))) :
      by rw [←hi.map_add_eq_smul_sub_map_sub, ←hi.map_add_eq_smul_sub_map_sub_rev]
     ...       = f x + f y :
      begin
        rw [←neg_sub x, hi.map_neg_of_map_zero h0, sub_neg_eq_add, sub_add_add_cancel, smul_add,
            two_smul, two_smul, ←two_smul ℝ (f x), ←two_smul ℝ (f y), ←mul_smul, ←mul_smul],
        simp
      end

/-- An isometry of real normed spaces with strictly convex codomain is a linear isometry if it
maps 0 to 0.  Unlike Mazur-Ulam, this does not require the isometry to be surjective.  -/
def linear_isometry_of_map_zero {f : F → E} (hi : isometry f) (h0 : f 0 = 0) :
  F →ₗᵢ[ℝ] E :=
{ to_fun := f,
  map_add' := hi.map_add_of_map_zero h0,
  map_smul' := hi.map_smul_of_map_zero h0,
  norm_map' := hi.norm_map_of_map_zero h0 }

@[simp] lemma coe_linear_isometry_of_map_zero {f : F → E} (hi : isometry f)
  (h0 : f 0 = 0) :
  ⇑(hi.linear_isometry_of_map_zero h0) = f :=
rfl

variables {PF : Type*} {PE : Type*} [metric_space PF] [metric_space PE]
variables [normed_add_torsor F PF] [normed_add_torsor E PE]
include E F

/-- An isometry of `normed_add_torsor`s for real normed spaces, strictly convex in the case of
the codomain, induces a linear isometry at any point.  Unlike Mazur-Ulam, this does not require
the isometry to be surjective.  -/
def linear_isometry_at {f : PF → PE} (hi : isometry f) (p : PF) : F →ₗᵢ[ℝ] E :=
linear_isometry_of_map_zero
  (show isometry (λ x : F, f (x +ᵥ p) -ᵥ f p), begin
    intros x y,
    simp_rw [edist_dist, dist_vsub_cancel_right, hi.dist_eq, dist_eq_norm_vsub,
             vadd_vsub_vadd_cancel_right, vsub_eq_sub]
   end) (by simp)

@[simp] lemma coe_linear_isometry_at {f : PF → PE} (hi : isometry f) (p : PF) :
  ⇑(hi.linear_isometry_at p) = λ x : F, f (x +ᵥ p) -ᵥ f p :=
rfl

lemma linear_isometry_at_apply {f : PF → PE} (hi : isometry f) (p : PF) (v : F) :
  hi.linear_isometry_at p v = f (v +ᵥ p) -ᵥ f p :=
rfl

lemma linear_isometry_at_apply_vsub {f : PF → PE} (hi : isometry f)
  (p₁ p₂ : PF) :
  hi.linear_isometry_at p₁ (p₂ -ᵥ p₁) +ᵥ f p₁ = f p₂ :=
by simp

lemma linear_isometry_at_eq {f : PF → PE} (hi : isometry f) (p₁ p₂ : PF) :
  hi.linear_isometry_at p₁ = hi.linear_isometry_at p₂ :=
begin
  ext x,
  rw [hi.linear_isometry_at_apply, hi.linear_isometry_at_apply,
      ←hi.linear_isometry_at_apply_vsub p₁ (x +ᵥ p₂), ←hi.linear_isometry_at_apply_vsub p₁ p₂,
      vadd_vsub_vadd_cancel_right, ←linear_isometry.map_sub, hi.linear_isometry_at_apply,
      vsub_sub_vsub_cancel_right, vadd_vsub]
end

/-- An isometry of `normed_add_torsor`s for real normed spaces, strictly convex in the case of
the codomain, is an affine isometry.  Unlike Mazur-Ulam, this does not require the isometry to
be surjective.  -/
noncomputable def affine_isometry_of_strict_convex_space {f : PF → PE} (hi : isometry f) :
  PF →ᵃⁱ[ℝ] PE :=
{ to_fun := f,
  linear := (hi.linear_isometry_at (classical.arbitrary PF)).to_linear_map,
  map_vadd' := λ p v, begin
    rw hi.linear_isometry_at_eq (classical.arbitrary PF) p,
    simp
  end,
  norm_map := (hi.linear_isometry_at _).norm_map }

@[simp] lemma coe_affine_isometry_of_strict_convex_space {f : PF → PE} (hi : isometry f) :
  ⇑(hi.affine_isometry_of_strict_convex_space) = f :=
rfl

lemma affine_isometry_of_strict_convex_space_apply {f : PF → PE} (hi : isometry f)
  (p : PF) :
  hi.affine_isometry_of_strict_convex_space p = f p :=
rfl

end isometry
