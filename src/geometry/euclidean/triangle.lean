/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
import geometry.euclidean.angle.oriented.affine
import geometry.euclidean.angle.unoriented.affine
import topology.metric_space.congruence
import tactic.interval_cases
import tactic.swap_var

/-!
# Triangles

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic geometrical results about distances and angles
in (possibly degenerate) triangles in real inner product spaces and
Euclidean affine spaces.  More specialized results, and results
developed for simplices in general rather than just for triangles, are
in separate files.  Definitions and results that make sense in more
general affine spaces rather than just in the Euclidean case go under
`linear_algebra.affine_space`.

## Implementation notes

Results in this file are generally given in a form with only those
non-degeneracy conditions needed for the particular result, rather
than requiring affine independence of the points of a triangle
unnecessarily.

## References

* https://en.wikipedia.org/wiki/Law_of_cosines
* https://en.wikipedia.org/wiki/Pons_asinorum
* https://en.wikipedia.org/wiki/Sum_of_angles_of_a_triangle

-/

noncomputable theory
open_locale big_operators
open_locale classical
open_locale real
open_locale real_inner_product_space

namespace inner_product_geometry

/-!
### Geometrical results on triangles in real inner product spaces

This section develops some results on (possibly degenerate) triangles
in real inner product spaces, where those definitions and results can
most conveniently be developed in terms of vectors and then used to
deduce corresponding results for Euclidean affine spaces.
-/

variables {V : Type*} [normed_add_comm_group V] [inner_product_space ℝ V]

/-- Law of cosines (cosine rule), vector angle form. -/
lemma norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
    (x y : V) :
  ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - 2 * ‖x‖ * ‖y‖ * real.cos (angle x y) :=
by rw [(show 2 * ‖x‖ * ‖y‖ * real.cos (angle x y) =
             2 * (real.cos (angle x y) * (‖x‖ * ‖y‖)), by ring),
       cos_angle_mul_norm_mul_norm, ←real_inner_self_eq_norm_mul_norm,
       ←real_inner_self_eq_norm_mul_norm, ←real_inner_self_eq_norm_mul_norm,
       real_inner_sub_sub_self, sub_add_eq_add_sub]

/-- Pons asinorum, vector angle form. -/
lemma angle_sub_eq_angle_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) :
  angle x (x - y) = angle y (y - x) :=
begin
  sorry
end

/-- Converse of pons asinorum, vector angle form. -/
lemma norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi {x y : V}
    (h : angle x (x - y) = angle y (y - x)) (hpi : angle x y ≠ π) : ‖x‖ = ‖y‖ :=
begin
  sorry
end

/-- The cosine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.cos (angle x (x - y) + angle y (y - x)) = -real.cos (angle x y) :=
begin
  by_cases hxy : x = y,
  { rw [hxy, angle_self hy],
    simp },
  { rw [real.cos_add, cos_angle, cos_angle, cos_angle],
    have hxn : ‖x‖ ≠ 0 := (λ h, hx (norm_eq_zero.1 h)),
    have hyn : ‖y‖ ≠ 0 := (λ h, hy (norm_eq_zero.1 h)),
    have hxyn : ‖x - y‖ ≠ 0 := (λ h, hxy (eq_of_sub_eq_zero (norm_eq_zero.1 h))),
    apply mul_right_cancel₀ hxn,
    apply mul_right_cancel₀ hyn,
    apply mul_right_cancel₀ hxyn,
    apply mul_right_cancel₀ hxyn,
    have H1 : real.sin (angle x (x - y)) * real.sin (angle y (y - x)) *
                ‖x‖ * ‖y‖ * ‖x - y‖ * ‖x - y‖ =
              (real.sin (angle x (x - y)) * (‖x‖ * ‖x - y‖)) *
                (real.sin (angle y (y - x)) * (‖y‖ * ‖x - y‖)), { ring },
    have H2 : ⟪x, x⟫ * (⟪x, x⟫ - ⟪x, y⟫ - (⟪x, y⟫ - ⟪y, y⟫)) -
                (⟪x, x⟫ - ⟪x, y⟫) * (⟪x, x⟫ - ⟪x, y⟫) =
              ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫, { ring },
    have H3 : ⟪y, y⟫ * (⟪y, y⟫ - ⟪x, y⟫ - (⟪x, y⟫ - ⟪x, x⟫)) -
                (⟪y, y⟫ - ⟪x, y⟫) * (⟪y, y⟫ - ⟪x, y⟫) =
              ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫, { ring },
    rw [mul_sub_right_distrib, mul_sub_right_distrib, mul_sub_right_distrib,
        mul_sub_right_distrib, H1, sin_angle_mul_norm_mul_norm, norm_sub_rev x y,
        sin_angle_mul_norm_mul_norm, norm_sub_rev y x, inner_sub_left, inner_sub_left,
        inner_sub_right, inner_sub_right, inner_sub_right, inner_sub_right, real_inner_comm x y, H2,
        H3, real.mul_self_sqrt (sub_nonneg_of_le (real_inner_mul_inner_self_le x y)),
        real_inner_self_eq_norm_mul_norm, real_inner_self_eq_norm_mul_norm,
        real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two],
    field_simp [hxn, hyn, hxyn],
    ring }
end

/-- The sine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma sin_angle_sub_add_angle_sub_rev_eq_sin_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.sin (angle x (x - y) + angle y (y - x)) = real.sin (angle x y) :=
begin
  by_cases hxy : x = y,
  { rw [hxy, angle_self hy],
    simp },
  { rw [real.sin_add, cos_angle, cos_angle],
    have hxn : ‖x‖ ≠ 0 := (λ h, hx (norm_eq_zero.1 h)),
    have hyn : ‖y‖ ≠ 0 := (λ h, hy (norm_eq_zero.1 h)),
    have hxyn : ‖x - y‖ ≠ 0 := (λ h, hxy (eq_of_sub_eq_zero (norm_eq_zero.1 h))),
    apply mul_right_cancel₀ hxn,
    apply mul_right_cancel₀ hyn,
    apply mul_right_cancel₀ hxyn,
    apply mul_right_cancel₀ hxyn,
    have H1 : real.sin (angle x (x - y)) * (⟪y, y - x⟫ / (‖y‖ * ‖y - x‖)) * ‖x‖ * ‖y‖ * ‖x - y‖ =
                real.sin (angle x (x - y)) * (‖x‖ * ‖x - y‖) *
                  (⟪y, y - x⟫ / (‖y‖ * ‖y - x‖)) * ‖y‖, { ring },
    have H2 : ⟪x, x - y⟫ / (‖x‖ * ‖y - x‖) * real.sin (angle y (y - x)) * ‖x‖ * ‖y‖ * ‖y - x‖ =
                ⟪x, x - y⟫ / (‖x‖ * ‖y - x‖) *
                  (real.sin (angle y (y - x)) * (‖y‖ * ‖y - x‖)) * ‖x‖, { ring },
    have H3 : ⟪x, x⟫ * (⟪x, x⟫ - ⟪x, y⟫ - (⟪x, y⟫ - ⟪y, y⟫)) -
                (⟪x, x⟫ - ⟪x, y⟫) * (⟪x, x⟫ - ⟪x, y⟫) =
              ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫, { ring },
    have H4 : ⟪y, y⟫ * (⟪y, y⟫ - ⟪x, y⟫ - (⟪x, y⟫ - ⟪x, x⟫)) -
                (⟪y, y⟫ - ⟪x, y⟫) * (⟪y, y⟫ - ⟪x, y⟫) =
              ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫  * ⟪x, y⟫, { ring },
    rw [right_distrib, right_distrib, right_distrib, right_distrib, H1,
        sin_angle_mul_norm_mul_norm, norm_sub_rev x y, H2, sin_angle_mul_norm_mul_norm,
        norm_sub_rev y x, mul_assoc (real.sin (angle x y)), sin_angle_mul_norm_mul_norm,
        inner_sub_left, inner_sub_left, inner_sub_right, inner_sub_right, inner_sub_right,
        inner_sub_right, real_inner_comm x y, H3, H4, real_inner_self_eq_norm_mul_norm,
        real_inner_self_eq_norm_mul_norm,
        real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two],
    field_simp [hxn, hyn, hxyn],
    ring }
end

/-- The cosine of the sum of the angles of a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma cos_angle_add_angle_sub_add_angle_sub_eq_neg_one {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.cos (angle x y + angle x (x - y) + angle y (y - x)) = -1 :=
by rw [add_assoc, real.cos_add, cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle hx hy,
       sin_angle_sub_add_angle_sub_rev_eq_sin_angle hx hy, mul_neg, ←neg_add',
       add_comm, ←sq, ←sq, real.sin_sq_add_cos_sq]

/-- The sine of the sum of the angles of a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma sin_angle_add_angle_sub_add_angle_sub_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.sin (angle x y + angle x (x - y) + angle y (y - x)) = 0 :=
begin
  rw [add_assoc, real.sin_add, cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle hx hy,
      sin_angle_sub_add_angle_sub_rev_eq_sin_angle hx hy],
  ring
end

/-- The sum of the angles of a possibly degenerate triangle (where the
two given sides are nonzero), vector angle form. -/
lemma angle_add_angle_sub_add_angle_sub_eq_pi {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  angle x y + angle x (x - y) + angle y (y - x) = π :=
begin
  have hcos := cos_angle_add_angle_sub_add_angle_sub_eq_neg_one hx hy,
  have hsin := sin_angle_add_angle_sub_add_angle_sub_eq_zero hx hy,
  rw real.sin_eq_zero_iff at hsin,
  cases hsin with n hn,
  symmetry' at hn,
  have h0 : 0 ≤ angle x y + angle x (x - y) + angle y (y - x) :=
    add_nonneg (add_nonneg (angle_nonneg _ _) (angle_nonneg _ _)) (angle_nonneg _ _),
  have h3 : angle x y + angle x (x - y) + angle y (y - x) ≤ π + π + π :=
    add_le_add (add_le_add (angle_le_pi _ _) (angle_le_pi _ _)) (angle_le_pi _ _),
  have h3lt : angle x y + angle x (x - y) + angle y (y - x) < π + π + π,
  { by_contradiction hnlt,
    have hxy : angle x y = π,
    { by_contradiction hxy,
      exact hnlt (add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le
                                           (lt_of_le_of_ne (angle_le_pi _ _) hxy)
                                         (angle_le_pi _ _)) (angle_le_pi _ _)) },
    rw hxy at hnlt,
    rw angle_eq_pi_iff at hxy,
    rcases hxy with ⟨hx, ⟨r, ⟨hr, hxr⟩⟩⟩,
    rw [hxr, ←one_smul ℝ x, ←mul_smul, mul_one, ←sub_smul, one_smul, sub_eq_add_neg,
        angle_smul_right_of_pos _ _ (add_pos zero_lt_one (neg_pos_of_neg hr)), angle_self hx,
        add_zero] at hnlt,
    apply hnlt,
    rw add_assoc,
    exact add_lt_add_left (lt_of_le_of_lt (angle_le_pi _ _)
                                          (lt_add_of_pos_right π real.pi_pos)) _ },
  have hn0 : 0 ≤ n,
  { rw [hn, mul_nonneg_iff_left_nonneg_of_pos real.pi_pos] at h0,
    norm_cast at h0,
    exact h0 },
  have hn3 : n < 3,
  { rw [hn, (show π + π + π = 3 * π, by ring)] at h3lt,
    replace h3lt := lt_of_mul_lt_mul_right h3lt (le_of_lt real.pi_pos),
    norm_cast at h3lt,
    exact h3lt },
  interval_cases n,
  { rw hn at hcos,
    simp at hcos,
    norm_num at hcos },
  { rw hn,
    norm_num },
  { rw hn at hcos,
    simp at hcos,
    norm_num at hcos },
end

end inner_product_geometry

namespace euclidean_geometry
/-!
### Geometrical results on triangles in Euclidean affine spaces

This section develops some geometrical definitions and results on
(possible degenerate) triangles in Euclidean affine spaces.
-/
open inner_product_geometry

open_locale euclidean_geometry

variables {V : Type*} {P : Type*}
  [normed_add_comm_group V] [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P]
include V

/-- **Law of cosines** (cosine rule), angle-at-point form. -/
lemma dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
    (p1 p2 p3 : P) :
  dist p1 p3 * dist p1 p3 =
    dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2 -
      2 * dist p1 p2 * dist p3 p2 * real.cos (∠ p1 p2 p3) :=
begin
  rw [dist_eq_norm_vsub V p1 p3, dist_eq_norm_vsub V p1 p2, dist_eq_norm_vsub V p3 p2],
  unfold angle,
  convert norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
          (p1 -ᵥ p2 : V) (p3 -ᵥ p2 : V),
  { exact (vsub_sub_vsub_cancel_right p1 p3 p2).symm },
  { exact (vsub_sub_vsub_cancel_right p1 p3 p2).symm }
end

alias dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle ← law_cos

/-- **cosine elimination**, using the cosine rule. -/
lemma cos_angle_elim (p1 p2 p3 : P) : real.cos (∠ p1 p2 p3) =
  (dist p1 p2 * dist p1 p2 + dist p2 p3 * dist p2 p3 - dist p1 p3 * dist p1 p3) /
    (2 * dist p1 p2 * dist p2 p3) :=
begin
  unfold angle, rw cos_angle,
  rw real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
  simp [ ← normed_add_torsor.dist_eq_norm'],
  rw [div_div, mul_assoc, dist_comm p2 p3],
end

/-- The **sum of the angles of a triangle** (possibly degenerate, where the
given vertex is distinct from the others), angle-at-point. -/
lemma angle_add_angle_add_angle_eq_pi {p1 p2 p3 : P} (h2 : p2 ≠ p1) (h3 : p3 ≠ p1) :
  ∠ p1 p2 p3 + ∠ p2 p3 p1 + ∠ p3 p1 p2 = π :=
begin
  rw [add_assoc, add_comm, add_comm (∠ p2 p3 p1), angle_comm p2 p3 p1],
  unfold angle,
  rw [←angle_neg_neg (p1 -ᵥ p3), ←angle_neg_neg (p1 -ᵥ p2), neg_vsub_eq_vsub_rev,
      neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev,
      ←vsub_sub_vsub_cancel_right p3 p2 p1, ←vsub_sub_vsub_cancel_right p2 p3 p1],
  exact angle_add_angle_sub_add_angle_sub_eq_pi (λ he, h3 (vsub_eq_zero_iff_eq.1 he))
                                                (λ he, h2 (vsub_eq_zero_iff_eq.1 he))
end

/-- The **sum of the angles of a triangle** (possibly degenerate, where the triangle is a line),
oriented angles at point. -/
lemma oangle_add_oangle_add_oangle_eq_pi
  [module.oriented ℝ V (fin 2)] [fact (finite_dimensional.finrank ℝ V = 2)] {p1 p2 p3 : P}
  (h21 : p2 ≠ p1) (h32 : p3 ≠ p2) (h13 : p1 ≠ p3) : ∡ p1 p2 p3 + ∡ p2 p3 p1 + ∡ p3 p1 p2 = π :=
by simpa only [neg_vsub_eq_vsub_rev] using
    positive_orientation.oangle_add_cyc3_neg_left
      (vsub_ne_zero.mpr h21) (vsub_ne_zero.mpr h32) (vsub_ne_zero.mpr h13)

/-- **sine elimination**, using the cosine rule -/
lemma sin_angle_elim (a b c : P) : real.sin (∠ a b c) =
  real.sqrt (1 - ((dist a b ^ 2 + dist b c ^ 2 - dist a c ^ 2) ^ 2) /
    (2 * dist a b * dist b c) ^ 2) :=
begin
  rw real.sin_eq_sqrt_one_sub_cos_sq
    (euclidean_geometry.angle_nonneg a b c)
    (euclidean_geometry.angle_le_pi a b c),
  rw [cos_angle_elim, ← pow_two, ← pow_two, ← pow_two, div_pow],
end

/-- **Law of sines** -/
lemma sine_rule {a b c : P} (hac : a ≠ c) (hbc : b ≠ c) :
  real.sin (∠ a b c) / dist a c = real.sin (∠ b a c) / dist b c :=
begin
  by_cases hab : a = b, rw hab, change a ≠ b at hab,
  rw ← dist_pos at hab hbc hac,

  have h₁ : 0 < 2 * dist a b * dist a c, simp [hab, hac],
  have h₂ : 0 < 2 * dist a b * dist b c, simp [hab, hbc],
  simp [sin_angle_elim, dist_comm],
  rw [sub_div', real.sqrt_div', real.sqrt_sq, div_div],
  rw [sub_div', real.sqrt_div', real.sqrt_sq, div_div],
  ring_nf,
  exact le_of_lt h₁, exact sq_nonneg _, exact pow_ne_zero 2 (ne_of_gt h₁),
  exact le_of_lt h₂, exact sq_nonneg _, exact pow_ne_zero 2 (ne_of_gt h₂),
end

section congruence

omit V

set_option class.instance_max_depth 38
private lemma fin_three {i₁ i₂ i₃ j₁ j₂ : fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
  (h : j₁ ≠ j₂) :
    (j₁ = i₁ ∧ j₂ = i₂) ∨ (j₁ = i₂ ∧ j₂ = i₁) ∨ (j₁ = i₁ ∧ j₂ = i₃) ∨
    (j₁ = i₃ ∧ j₂ = i₁) ∨ (j₁ = i₂ ∧ j₂ = i₃) ∨ (j₁ = i₃ ∧ j₂ = i₂) :=
by dec_trivial!




private lemma dist_eq_comm {P P₂ : Type*} {a b : P} {c d : P₂} [pseudo_metric_space P]
  [pseudo_metric_space P₂] :
  dist a b = dist c d ↔ dist b a = dist d c :=
by rw [dist_comm b a, dist_comm d c]

open_locale congruence

section SSS

variables {P₁ P₂ : Type*}
  [pseudo_metric_space P₁] [pseudo_metric_space P₂]
  {a b c : P} {d e f : P₂}
  {t1 : fin 3 → P₁} {t2 : fin 3 → P₂} {i₁ i₂ i₃ : fin 3}

/-- SSS congruence -/
lemma side_side_side'' (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
  (hs₁ : dist (t1 i₁) (t1 i₂) = dist (t2 i₁) (t2 i₂))
  (hs₂ : dist (t1 i₁) (t1 i₃) = dist (t2 i₁) (t2 i₃))
  (hs₃ : dist (t1 i₂) (t1 i₃) = dist (t2 i₂) (t2 i₃)) :
    t1 ≅ t2 :=
begin
  apply congruence.of_pairwise_dist_eq,
  intros j₁ j₂ h,
  { rcases fin_three h₁₂ h₁₃ h₂₃ h with
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩);
      try {assumption}; rwa dist_eq_comm },
end

/-- SSS congruence -/
lemma side_side_side' (hs₁ : dist (t1 0) (t1 1) = dist (t2 0) (t2 1))
  (hs₂ : dist (t1 0) (t1 2) = dist (t2 0) (t2 2))
  (hs₃ : dist (t1 1) (t1 2) = dist (t2 1) (t2 2)) :
    t1 ≅ t2 :=
by refine side_side_side'' _ _ _ hs₁ hs₂ hs₃; dec_trivial

/-- SSS congruence -/
lemma side_side_side (hs₁ : dist a b = dist d e)
  (hs₂ : dist a c = dist d f) (hs₃ : dist b c = dist e f) : ![a,b,c] ≅ ![d,e,f] :=
side_side_side' hs₁ hs₂ hs₃

end SSS -- section

variables {V₂ : Type*} {P₂ : Type*} [inner_product_space ℝ V₂] [metric_space P₂]
    [normed_add_torsor V₂ P₂]
    {a b c : P} {d e f : P₂}
    {t1 : fin 3 → P} {t2 : fin 3 → P₂} {i₁ i₂ i₃ : fin 3}
include V V₂

/-- SAS congruence -/
private lemma side_angle_side'' (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
  (ha : ∠ (t1 i₁) (t1 i₂) (t1 i₃) = ∠ (t2 i₁) (t2 i₂) (t2 i₃))
  (hs₁ : dist (t1 i₁) (t1 i₂) = dist (t2 i₁) (t2 i₂))
  (hs₂ : dist (t1 i₂) (t1 i₃) = dist (t2 i₂) (t2 i₃)) :
  t1 ≅ t2 :=
begin
  refine side_side_side'' h₁₂ h₁₃ h₂₃ hs₁ _ hs₂,
  by_cases h : dist (t1 i₁) (t1 i₂) = 0,
  { rw h at hs₁,
    rwa [dist_eq_zero.1 h, dist_eq_zero.1 hs₁.symm] },
  by_cases h' : dist (t1 i₂) (t1 i₃) = 0,
  { rw h' at hs₂,
    rwa [← dist_eq_zero.1 h', ← dist_eq_zero.1 hs₂.symm] },

  apply_fun real.cos at ha,
  simp [cos_angle_elim, ← hs₁, ← hs₂] at ha,
  rw div_left_inj'
    (mul_ne_zero_iff.2 ⟨mul_ne_zero_iff.2 ⟨show (2:ℝ) ≠ 0, from by simp, h⟩, h'⟩) at ha,
  rw sub_right_inj at ha,
  rw [← pow_two , ← pow_two] at ha,
  rw sq_eq_sq dist_nonneg dist_nonneg at ha,
  exact ha,
end

/-- SAS congruence -/
lemma side_angle_side₁' (ha : ∠ (t1 1) (t1 0) (t1 2) = ∠ (t2 1) (t2 0) (t2 2))
  (hs₁ : dist (t1 0) (t1 1) = dist (t2 0) (t2 1)) (hs₂ : dist (t1 0) (t1 2) = dist (t2 0) (t2 2)) :
  t1 ≅ t2 :=
by refine side_angle_side'' _ _ _ ha (dist_eq_comm.1 hs₁) hs₂; dec_trivial

/-- SAS congruence -/
lemma side_angle_side₂' (ha : ∠ (t1 0) (t1 1) (t1 2) = ∠ (t2 0) (t2 1) (t2 2))
  (hs₁ : dist (t1 0) (t1 1) = dist (t2 0) (t2 1)) (hs₂ : dist (t1 1) (t1 2) = dist (t2 1) (t2 2)) :
  t1 ≅ t2 :=
by refine side_angle_side'' _ _ _ ha hs₁ hs₂; dec_trivial

/-- SAS congruence -/
lemma side_angle_side₃' (ha : ∠ (t1 0) (t1 2) (t1 1) = ∠ (t2 0) (t2 2) (t2 1))
  (hs₁ : dist (t1 0) (t1 2) = dist (t2 0) (t2 2)) (hs₂ : dist (t1 1) (t1 2) = dist (t2 1) (t2 2)) :
  t1 ≅ t2 :=
by refine side_angle_side'' _ _ _ ha hs₁ (dist_eq_comm.1 hs₂); dec_trivial

/-- SAS congruence -/
lemma side_angle_side₁ (ha : ∠ b a c = ∠ e d f) (hs₁ : dist a b = dist d e)
  (hs₂ : dist a c = dist d f) : ![a,b,c] ≅ ![d,e,f] :=
side_angle_side₁' ha hs₁ hs₂

/-- SAS congruence -/
lemma side_angle_side₂ (ha : ∠ a b c = ∠ d e f) (hs₁ : dist a b = dist d e)
  (hs₂ : dist b c = dist e f) : ![a,b,c] ≅ ![d,e,f] :=
side_angle_side₂' ha hs₁ hs₂

/-- SAS congruence -/
lemma side_angle_side₃ (ha : ∠ a c b = ∠ d f e) (hs₁ : dist a c = dist d f)
  (hs₂ : dist b c = dist e f) : ![a,b,c] ≅ ![d,e,f] :=
side_angle_side₃' ha hs₁ hs₂



-- lemma angle_angle_side (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
--   (ha₁ : ∠ (t1 i₁) (t1 i₂) (t1 i₃) = ∠ (t2 i₁) (t2 i₂) (t2 i₃))
--   (ha₂ : ∠ (t1 i₂) (t1 i₁) (t1 i₃) = ∠ (t2 i₂) (t2 i₁) (t2 i₃))
--   (hs : dist (t1 i₂) (t1 i₃) = dist (t2 i₂) (t2 i₃))
--   (h1 : ¬ collinear ℝ ({(t1 i₁), (t1 i₂), (t1 i₃)} : set P))
--   (h2 : ¬ collinear ℝ ({(t2 i₁), (t2 i₂), (t2 i₃)} : set P₂)) :
--     ![(t1 i₁),(t1 i₂),(t1 i₃)] ≅ ![(t2 i₁),(t2 i₂),(t2 i₃)] :=
-- begin
--   have ha₃ := angle_add_angle_add_angle_eq_pi
--     (ne₁₃_of_not_collinear h1) (ne₂₃_of_not_collinear h1),
--   rw ← angle_add_angle_add_angle_eq_pi
--     (ne₁₃_of_not_collinear h2) (ne₂₃_of_not_collinear h2) at ha₃,
--   simp only [angle_comm] at ha₃,
--   rw [ha₁, ha₂, add_left_cancel_iff] at ha₃,

--   have s := sine_rule (ne₁₃_of_not_collinear h1) (ne₂₃_of_not_collinear h1),
--   have s':= sine_rule (ne₁₃_of_not_collinear h2) (ne₂₃_of_not_collinear h2),
--   rw [ha₁, ha₂, hs] at s,
--   rw ← s' at s,
--   rw [div_eq_mul_inv, div_eq_mul_inv] at s,
--   rw mul_right_inj' at s, swap, -- apply sine lemma here
--   { apply ne_of_gt,
--     apply real.sin_pos_of_pos_of_lt_pi,
--     apply angle_pos_of_not_collinear h2,
--     apply angle_lt_pi_of_not_collinear h2 },
--   rw inv_inj at s,
--   -- rw [dist_comm c b, dist_comm f e] at hs,
--   -- apply side_angle_side'' h₁₂ h₁₃ h₂₃ ha₃ s hs,
-- end

end congruence -- section

/-- **Isosceles Triangle Theorem**: Pons asinorum, angle-at-point form. -/
lemma angle_eq_angle_of_dist_eq {p1 p2 p3 : P} (h : dist p1 p2 = dist p1 p3) :
  ∠ p1 p2 p3 = ∠ p1 p3 p2 :=
begin
  sorry
end

/-- Converse of pons asinorum, angle-at-point form. -/
lemma dist_eq_of_angle_eq_angle_of_angle_ne_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = ∠ p1 p3 p2)
    (hpi : ∠ p2 p1 p3 ≠ π) : dist p1 p2 = dist p1 p3 :=
begin
  sorry
end





/-- **Stewart's Theorem**. -/
theorem dist_sq_mul_dist_add_dist_sq_mul_dist (a b c p : P) (h : ∠ b p c = π) :
  dist a b ^ 2 * dist c p + dist a c ^ 2 * dist b p =
  dist b c * (dist a p ^ 2 + dist b p * dist c p) :=
begin
  rw [pow_two, pow_two, law_cos a p b, law_cos a p c,
      eq_sub_of_add_eq (angle_add_angle_eq_pi_of_angle_eq_pi a h), real.cos_pi_sub,
      dist_eq_add_dist_of_angle_eq_pi h],
  ring,
end

/-- **Apollonius's Theorem**. -/
theorem dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq (a b c : P) :
  dist a b ^ 2 + dist a c ^ 2 = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) :=
begin
  by_cases hbc : b = c,
  { simp [hbc, midpoint_self, dist_self, two_mul] },
  { let m := midpoint ℝ b c,
    have : dist b c ≠ 0 := (dist_pos.mpr hbc).ne',
    have hm := dist_sq_mul_dist_add_dist_sq_mul_dist a b c m (angle_midpoint_eq_pi b c hbc),
    simp only [dist_left_midpoint, dist_right_midpoint, real.norm_two] at hm,
    calc  dist a b ^ 2 + dist a c ^ 2
        = 2 / dist b c * (dist a b ^ 2 * (2⁻¹ * dist b c) + dist a c ^ 2 * (2⁻¹ * dist b c)) :
          by { field_simp, ring }
    ... = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) :
          by { rw hm, field_simp, ring } },
end

lemma dist_mul_of_eq_angle_of_dist_mul (a b c a' b' c' : P) (r : ℝ) (h : ∠ a' b' c' = ∠ a b c)
  (hab : dist a' b' = r * dist a b) (hcb : dist c' b' = r * dist c b) :
  dist a' c' = r * dist a c :=
begin
  have h' : dist a' c' ^ 2 = (r * dist a c) ^ 2,
    calc  dist a' c' ^ 2
        = dist a' b' ^ 2 + dist c' b' ^ 2 - 2 * dist a' b' * dist c' b' * real.cos (∠ a' b' c') :
          by { simp [pow_two, law_cos a' b' c'] }
    ... = r ^ 2 * (dist a b ^ 2 + dist c b ^ 2 - 2 * dist a b * dist c b * real.cos (∠ a b c)) :
          by { rw [h, hab, hcb], ring }
    ... = (r * dist a c) ^ 2 : by simp [pow_two, ← law_cos a b c, mul_pow],
  by_cases hab₁ : a = b,
  { have hab'₁ : a' = b', { rw [← dist_eq_zero, hab, dist_eq_zero.mpr hab₁, mul_zero r] },
    rw [hab₁, hab'₁, dist_comm b' c', dist_comm b c, hcb] },
  { have h1 : 0 ≤ r * dist a b, { rw ← hab, exact dist_nonneg },
    have h2 : 0 ≤ r := nonneg_of_mul_nonneg_left h1 (dist_pos.mpr hab₁),
    exact (sq_eq_sq dist_nonneg (mul_nonneg h2 dist_nonneg)).mp h' },
end

end euclidean_geometry
