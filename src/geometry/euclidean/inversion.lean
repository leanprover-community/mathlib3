/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import geometry.euclidean.basic

/-!
# Inversion in an affine space

In this file we define inversion in a sphere in an affine space. This map sends each point `x` to
the point `y` such that `y -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c)`, where `c` and `R` are the center
and the radius the sphere.

In many applications, it is convenient to assume that the inversions swaps the center and the point
at infinity. In order to stay in the original affine space, we define the map so that it sends
center to itself.

Currently, we prove only a few basic lemmas needed to prove Ptolemy's inequality, see
`euclidean_geometry.mul_dist_le_mul_dist_add_mul_dist`.
-/

noncomputable theory
open metric real

namespace euclidean_geometry

variables {V P : Type*} [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P]
  {a b c d x y z : P} {R : ℝ}

include V

/-- Inversion in a sphere in an affine space. This map sends each point `x` to the point `y` such
that `y -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c)`, where `c` and `R` are the center and the radius the
sphere. -/
def inversion (c : P) (R : ℝ) (x : P) : P := (R / dist x c) ^ 2 • (x -ᵥ c) +ᵥ c

@[simp] lemma inversion_self (c : P) (R : ℝ) : inversion c R c = c := by simp [inversion]

@[simp] lemma inversion_dist_center (c x : P) : inversion c (dist x c) x = x :=
begin
  rcases eq_or_ne x c with rfl|hne,
  { apply inversion_self },
  { rw [inversion, div_self, one_pow, one_smul, vsub_vadd],
    rwa [dist_ne_zero] }
end

lemma inversion_of_mem_sphere (h : x ∈ sphere c R) : inversion c R x = x :=
h.out ▸ inversion_dist_center c x

/-- Distance from the image of a point under inversion to the center. This formula accidentally
works for `x = c`. -/
lemma dist_inversion_center (c x : P) (R : ℝ) : dist (inversion c R x) c = R ^ 2 / dist x c :=
begin
  rcases eq_or_ne x c with (rfl|hx), { simp },
  have : dist x c ≠ 0, from dist_ne_zero.2 hx,
  field_simp [inversion, norm_smul, norm_eq_abs, abs_div, ← dist_eq_norm_vsub, sq, mul_assoc]
end

/-- Distance between the images of two points under an inversion. -/
lemma dist_inversion_inversion (hx : x ≠ c) (hy : y ≠ c) (R : ℝ) :
  dist (inversion c R x) (inversion c R y) = (R ^ 2 / (dist x c * dist y c)) * dist x y :=
begin
  dunfold inversion,
  simp_rw [dist_vadd_cancel_right, dist_eq_norm_vsub V _ c],
  simpa only [dist_vsub_cancel_right]
    using dist_div_norm_sq_smul (vsub_ne_zero.2 hx) (vsub_ne_zero.2 hy) R
end

/-- **Ptolemy's inequality**: in a quadrangle `ABCD`, `|AC| * |BD| ≤ |AB| * |CD| + |BC| * |AD|`. If
`ABCD` is a convex cyclic polygon, then this inequality becomes an equality, see
`euclidean_geometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`.  -/
lemma mul_dist_le_mul_dist_add_mul_dist (a b c d : P) :
  dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d :=
begin
  rcases eq_or_ne b a with rfl|hb,
  { rw [dist_self, zero_mul, zero_add] },
  rcases eq_or_ne c a with rfl|hc,
  { rw [dist_self, zero_mul],
    apply_rules [add_nonneg, mul_nonneg, dist_nonneg] },
  rcases eq_or_ne d a with rfl|hd,
  { rw [dist_self, mul_zero, add_zero, dist_comm d, dist_comm d, mul_comm] },
  have H := dist_triangle (inversion a 1 b) (inversion a 1 c) (inversion a 1 d),
  rw [dist_inversion_inversion hb hd, dist_inversion_inversion hb hc,
    dist_inversion_inversion hc hd, one_pow] at H,
  rw [← dist_pos] at hb hc hd,
  rw [← div_le_div_right (mul_pos hb (mul_pos hc hd))],
  convert H; { field_simp [hb.ne', hc.ne', hd.ne', dist_comm a], ring }
end

end euclidean_geometry
