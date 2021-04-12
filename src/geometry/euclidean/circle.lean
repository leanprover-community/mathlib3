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
  have hzy : ⟪z, y⟫ = 0,
  { rw [← eq_of_pow_two_eq_pow_two (norm_nonneg (z - y)) (norm_nonneg (z + y)),
        norm_add_pow_two_real, norm_sub_pow_two_real] at h₂,
    linarith },

  let l : ℝ := 1,
  have hk₂ : (k - 1) ≠ 0 := sub_ne_zero.mpr hk_ne_one,

  have h5 : (k - l) • x - (k + l) • y = 0,
  { calc  (k - l) • x - (k + l) • y
        = (k • x - l • x) - (k • y + l • y) : by rw [sub_smul k l x, add_smul k l y]
    ... = (k • x - x) - (k • y + y)         : by rw [one_smul, one_smul]
    ... = (k • x - k • y) - (x + y)         : by rw [sub_sub (k • x) x ((k • y) + y),
                                                     add_left_comm x (k • y) y,
                                                     sub_add_eq_sub_sub (k • x) (k • y) (x + y)]
    ... = k • (x - y) - (x + y)             : by rw ← smul_sub k x y
    ... = 0                                 : sub_eq_zero.mpr hk.symm },

  let r : ℝ := (k - 1)⁻¹ * (k + 1),

  have hxy : x = r • y,
  { rw ← smul_smul (k - 1)⁻¹ (k + 1) y,
    rw eq_inv_smul_iff' hk₂,
    exact sub_eq_zero.mp h5 },

  have hzx : ⟪z, x⟫ = 0, { rw [hxy, inner_smul_right, hzy, mul_zero] },

  have hl_smul_y_eq_y : l • y = y, { rw one_smul },

  refine eq.symm _,

  calc  abs (∥z + y∥ ^ 2 - ∥z - x∥ ^ 2)
      = abs (- (∥x∥ ^ 2 - ∥y∥ ^ 2))          : by { rw [norm_add_pow_two_real, hzy,
                                                      norm_sub_pow_two_real, hzx], ring_nf }
  ... = abs (∥x∥ ^ 2 - ∥y∥ ^ 2)              : by rw ← abs_neg (∥x∥ ^ 2 - ∥y∥ ^ 2)
  ... = abs (∥r • y∥ ^ 2 - ∥y∥ ^ 2)          : by rw hxy
  ... = abs (((abs r) * ∥y∥) ^ 2 - ∥y∥ ^ 2)  : by rw [norm_smul r y, real.norm_eq_abs r]
  ... = abs ((r ^ 2 * ∥y∥ ^ 2) - ∥y∥ ^ 2)    : by rw [mul_pow _ _ 2, pow_even_abs (_) (even_bit0 1)]
  ... = abs ((r ^ 2 - 1) * ∥y∥ ^ 2)         : by ring_nf
  ... = abs ((r ^ 2 - l ^ 2) * ∥y∥ ^ 2)     : by norm_num
  ... = abs (r ^ 2 - l ^ 2) * abs (∥y∥ ^ 2) : by rw ← abs_mul _ _
  ... = abs (r ^ 2 - l ^ 2) * ∥y∥ ^ 2       : by rw abs_of_nonneg (pow_two_nonneg ∥y∥)
  ... = abs ((r - l) * (r + l)) * ∥y∥ ^ 2  : by rw (show r ^ 2 - l ^ 2 = (r - l) * (r + l), by ring)
  ... = abs (r - l) * abs(r + l) * ∥y∥ ^ 2  : by rw abs_mul (r - l) (r + l)
  ... = (∥r - l∥ * ∥r + l∥) * ∥y∥ ^ 2         : by rw [← real.norm_eq_abs _, ← real.norm_eq_abs _]
  ... = (∥r - l∥ * ∥y∥) * (∥r + l∥ * ∥y∥)      : by ring
  ... = ∥(r - l) • y∥ * ∥(r + l) • y∥        : by rw [← norm_smul (r - l) y, ← norm_smul (r + l) y]
  ... = ∥r • y - l • y∥ * ∥r • y + l • y∥    : by rw [sub_smul r l y, add_smul r l y]
  ... = ∥r • y - y∥ * ∥r • y + y∥            : by rw hl_smul_y_eq_y
  ... = ∥x - y∥ * ∥x + y∥                    : by rw ← hxy,
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
  set circle : set P := {a, b, c, d} with circle_def,
  obtain ⟨q, r, h⟩ := (cospherical_def circle).mp h,
  have ha₀ : a ∈ circle, finish,
  have hb₀ : b ∈ circle, finish,
  have hc₀ : c ∈ circle, finish,
  have hd₀ : d ∈ circle, finish,
  obtain ⟨ha₁, hb₁, hc₁, hd₁⟩ := ⟨h a ha₀, h b hb₀, h c hc₀, h d hd₀⟩,

  have hqab : dist a q = dist b q, { rwa ← hb₁ at ha₁ },
  have hqcd : dist c q = dist d q, { rwa ← hd₁ at hc₁ },

  obtain habpq := mul_dist_eq_sub_dist_pow_two hapb hqab,
  obtain hcdpq := mul_dist_eq_sub_dist_pow_two hcpd hqcd,
  rw [habpq, hcdpq, hb₁, hd₁],
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
