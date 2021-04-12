/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import geometry.euclidean.basic

/-!
# Circles

This file proves basic geometrical results about distances and angles
in circles in real inner product spaces and Euclidean affine spaces.
-/

open_locale euclidean_geometry real_inner_product_space real

variables {V : Type*} [inner_product_space ℝ V]

namespace inner_product_geometry
/-!
### Geometrical results on circles in real inner product spaces

This section develops some results on circles in real inner product spaces,
which are used to deduce corresponding results for Euclidean affine spaces.
-/

lemma mul_norm_eq_sub_norm_pow_two {x y z : V} (h₁ : ∃ k : ℝ, k ≠ 1 ∧ x + y = k • (x - y))
  (h₂ : ∥z - y∥ = ∥z + y∥) : ∥x - y∥ * ∥x + y∥ = abs (∥z + y∥ ^ 2 - ∥z - x∥ ^ 2) :=
begin
  obtain ⟨k, hk_ne_one, hk⟩ := h₁,
  let r := (k - 1)⁻¹ * (k + 1),

  have hxy : x = r • y,
  { rw [← smul_smul, eq_inv_smul_iff' (sub_ne_zero.mpr hk_ne_one), ← sub_eq_zero],
    calc  (k - 1) • x - (k + 1) • y
        = (k • x - x) - (k • y + y) : by simp_rw [sub_smul, add_smul, one_smul]
    ... = (k • x - k • y) - (x + y) : by simp_rw [← sub_sub, sub_right_comm]
    ... = k • (x - y) - (x + y)     : by rw ← smul_sub k x y
    ... = 0                         : sub_eq_zero.mpr hk.symm },

  have hzy : ⟪z, y⟫ = 0,
  { rw [← eq_of_pow_two_eq_pow_two (norm_nonneg (z - y)) (norm_nonneg (z + y)),
        norm_add_pow_two_real, norm_sub_pow_two_real] at h₂,
    linarith },

  have hzx : ⟪z, x⟫ = 0 := by rw [hxy, inner_smul_right, hzy, mul_zero],

  symmetry,

  calc  abs (∥z + y∥ ^ 2 - ∥z - x∥ ^ 2)
      = abs (∥x∥ ^ 2 - ∥y∥ ^ 2)            : by simp [norm_add_pow_two_real, norm_sub_pow_two_real,
                                                    hzy, hzx, abs_sub]
  ... = abs (∥r∥ ^ 2 * ∥y∥ ^ 2 - ∥y∥ ^ 2)   : by rw [hxy, norm_smul, mul_pow]
  ... = abs (r ^ 2 * ∥y∥ ^ 2 - ∥y∥ ^ 2)    : by rw [real.norm_eq_abs, sqr_abs]
  ... = abs ((r - 1) * (r + 1) * ∥y∥ ^ 2) : by ring_nf
  ... = ∥r - 1∥ * ∥r + 1∥ * ∥y∥ ^ 2         : by simp [abs_mul, real.norm_eq_abs]
  ... = ∥r - 1∥ * ∥y∥ * (∥r + 1∥ * ∥y∥)      : by ring
  ... = ∥(r - 1) • y∥ * ∥(r + 1) • y∥      : by simp_rw [norm_smul]
  ... = ∥x - y∥ * ∥x + y∥                  : by simp [sub_smul, add_smul, hxy],
end

end inner_product_geometry

namespace euclidean_geometry
/-!
### Geometrical results on circles in Euclidean affine spaces

This section develops some results on circles in Euclidean affine spaces.
-/

open inner_product_geometry

variables {P : Type*} [metric_space P] [normed_add_torsor V P]
include V

/-- If `P` is a point on the line `AB` and `Q` is equidistant from `A` and `B`, then
`AP * BP = abs (BQ ^ 2 - PQ ^ 2)`. -/
lemma mul_dist_eq_sub_dist_pow_two {a b p q : P} (hp : ∃ k : ℝ, k ≠ 1 ∧ b -ᵥ p = k • (a -ᵥ p))
  (hq : dist a q = dist b q) : (dist a p) * (dist b p) = abs ((dist b q) ^ 2 - (dist p q) ^ 2) :=
begin
  let m : P := midpoint ℝ a b,
  have h1 : a -ᵥ p = (m -ᵥ p) - (m -ᵥ a) := (vsub_sub_vsub_cancel_left a p m).symm,
  have h2 : b -ᵥ p = (m -ᵥ p) + (m -ᵥ a),
  { rw [midpoint_vsub_left a b, ← right_vsub_midpoint a b, add_comm, vsub_add_vsub_cancel b m p] },
  have h3 : a -ᵥ q = (m -ᵥ q) - (m -ᵥ a) := (vsub_sub_vsub_cancel_left a q m).symm,
  have h4 : b -ᵥ q = (m -ᵥ q) + (m -ᵥ a),
  { rw [midpoint_vsub_left a b, ← right_vsub_midpoint a b, add_comm, vsub_add_vsub_cancel b m q] },
  have h5 : p -ᵥ q = (m -ᵥ q) - (m -ᵥ p) := (vsub_sub_vsub_cancel_left p q m).symm,

  rw [dist_eq_norm_vsub V a p, dist_eq_norm_vsub V b p, h1, h2],
  rw [dist_eq_norm_vsub V b q, dist_eq_norm_vsub V p q, h4, h5],
  rw [dist_eq_norm_vsub V a q, dist_eq_norm_vsub V b q, h3, h4] at hq,
  rw [h1, h2] at hp,
  exact mul_norm_eq_sub_norm_pow_two hp hq,
end

/-- If `A`, `B`, `C`, `D` are cospherical and `P` is on both lines `AB` and `CD`, then
`AP * BP = CP * DP` .-/
theorem mul_dist_eq_mul_dist_of_cospherical
  {a b c d p : P} (h : cospherical ({a, b, c, d} : set P))
  (hapb : ∃ k₁ : ℝ, k₁ ≠ 1 ∧ b -ᵥ p = k₁ • (a -ᵥ p))
  (hcpd : ∃ k₂ : ℝ, k₂ ≠ 1 ∧ d -ᵥ p = k₂ • (c -ᵥ p)) :
  (dist a p) * (dist b p) = (dist c p) * (dist d p) :=
begin
  obtain ⟨q, r, h'⟩ := (cospherical_def {a, b, c, d}).mp h,
  obtain ⟨ha, hb, hc, hd⟩ := ⟨h' a _, h' b _, h' c _, h' d _⟩,
  { rw ← hb at ha,
    rw ← hd at hc,
    rw [mul_dist_eq_sub_dist_pow_two hapb ha, mul_dist_eq_sub_dist_pow_two hcpd hc, hb, hd] },
  all_goals { simp },
end

/-- Intersecting Chords Theorem. -/
theorem intersecting_chords_theorem
  {a b c d p : P} (h : cospherical ({a, b, c, d} : set P))
  (hapb : ∠ a p b = π ) (hcpd : ∠ c p d = π ) :
  (dist a p) * (dist b p) = (dist c p) * (dist d p) :=
begin
  unfold angle at hapb,
  unfold angle at hcpd,
  obtain ⟨_, k₁, hk₁, hab₁⟩ := inner_product_geometry.angle_eq_pi_iff.mp hapb,
  obtain ⟨_, k₂, hk₂, hcd₁⟩ := inner_product_geometry.angle_eq_pi_iff.mp hcpd,
  have hk₁_ne_one : k₁ ≠ 1, linarith,
  have hk₂_ne_one : k₂ ≠ 1, linarith,
  exact mul_dist_eq_mul_dist_of_cospherical h ⟨k₁, hk₁_ne_one, hab₁⟩ ⟨k₂, hk₂_ne_one, hcd₁⟩,
end

/-- Intersecting Secants Theorem. -/
theorem intersecting_secants_theorem
  (a b c d p : P) (h : cospherical ({a, b, c, d} : set P))
  (hab : a ≠ b) (hcd : c ≠ d) (hapb : ∠ a p b = 0 ) (hcpd : ∠ c p d = 0 ) :
  (dist a p) * (dist b p) = (dist c p) * (dist d p) :=
begin
  unfold angle at hapb,
  unfold angle at hcpd,
  obtain ⟨_, k₁, _, hab₁⟩ := inner_product_geometry.angle_eq_zero_iff.mp hapb,
  obtain ⟨_, k₂, _, hcd₁⟩ := inner_product_geometry.angle_eq_zero_iff.mp hcpd,
  have hk₁_ne_one : k₁ ≠ 1,
  { by_contra, push_neg at h, rw [h, one_smul] at hab₁, apply hab,
    rw [← vsub_vadd a p, ← vsub_vadd b p, hab₁] },
  have hk₂_ne_one : k₂ ≠ 1,
  { by_contra, push_neg at h, rw [h, one_smul] at hcd₁, apply hcd,
    rw [← vsub_vadd c p, ← vsub_vadd d p, hcd₁] },
  exact mul_dist_eq_mul_dist_of_cospherical h ⟨k₁, hk₁_ne_one, hab₁⟩ ⟨k₂, hk₂_ne_one, hcd₁⟩,
end

end euclidean_geometry
