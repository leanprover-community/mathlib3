/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import geometry.euclidean.angle.oriented.right_angle
import geometry.euclidean.circumcenter

/-!
# Angles in circles and sphere.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves results about angles in circles and spheres.

-/

noncomputable theory

open finite_dimensional complex
open_locale euclidean_geometry real real_inner_product_space complex_conjugate

namespace orientation

variables {V : Type*} [normed_add_comm_group V] [inner_product_space ℝ V]
variables [fact (finrank ℝ V = 2)] (o : orientation ℝ V (fin 2))

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form. -/
lemma oangle_eq_two_zsmul_oangle_sub_of_norm_eq {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z)
  (hxy : ‖x‖ = ‖y‖) (hxz : ‖x‖ = ‖z‖) : o.oangle y z = (2 : ℤ) • o.oangle (y - x) (z - x) :=
begin
  have hy : y ≠ 0,
  { rintro rfl,
    rw [norm_zero, norm_eq_zero] at hxy,
    exact hxyne hxy },
  have hx : x ≠ 0 := norm_ne_zero_iff.1 (hxy.symm ▸ norm_ne_zero_iff.2 hy),
  have hz : z ≠ 0 := norm_ne_zero_iff.1 (hxz ▸ norm_ne_zero_iff.2 hx),
  calc o.oangle y z = o.oangle x z - o.oangle x y : (o.oangle_sub_left hx hy hz).symm
       ...           = (π - (2 : ℤ) • o.oangle (x - z) x) -
                       (π - (2 : ℤ) • o.oangle (x - y) x) :
         by rw [o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxzne.symm hxz.symm,
                o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxyne.symm hxy.symm]
       ...           = (2 : ℤ) • (o.oangle (x - y) x - o.oangle (x - z) x) : by abel
       ...           = (2 : ℤ) • o.oangle (x - y) (x - z) :
         by rw o.oangle_sub_right (sub_ne_zero_of_ne hxyne) (sub_ne_zero_of_ne hxzne) hx
       ...           = (2 : ℤ) • o.oangle (y - x) (z - x) :
         by rw [←oangle_neg_neg, neg_sub, neg_sub]
end

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form with radius specified. -/
lemma oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z)
  {r : ℝ} (hx : ‖x‖ = r) (hy : ‖y‖ = r) (hz : ‖z‖ = r) :
  o.oangle y z = (2 : ℤ) • o.oangle (y - x) (z - x) :=
o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq hxyne hxzne (hy.symm ▸ hx) (hz.symm ▸ hx)

/-- Oriented vector angle version of "angles in same segment are equal" and "opposite angles of
a cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same
result), represented here as equality of twice the angles. -/
lemma two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq {x₁ x₂ y z : V} (hx₁yne : x₁ ≠ y)
  (hx₁zne : x₁ ≠ z) (hx₂yne : x₂ ≠ y) (hx₂zne : x₂ ≠ z) {r : ℝ} (hx₁ : ‖x₁‖ = r) (hx₂ : ‖x₂‖ = r)
  (hy : ‖y‖ = r) (hz : ‖z‖ = r) :
  (2 : ℤ) • o.oangle (y - x₁) (z - x₁) = (2 : ℤ) • o.oangle (y - x₂) (z - x₂) :=
o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₁yne hx₁zne hx₁ hy hz ▸
  o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₂yne hx₂zne hx₂ hy hz

end orientation

namespace euclidean_geometry

variables {V : Type*} {P : Type*}
  [normed_add_comm_group V] [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P]
  [hd2 : fact (finrank ℝ V = 2)] [module.oriented ℝ V (fin 2)]
include hd2

local notation `o` := module.oriented.positive_orientation

namespace sphere

/-- Angle at center of a circle equals twice angle at circumference, oriented angle version. -/
lemma oangle_center_eq_two_zsmul_oangle {s : sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s)
  (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₃ : p₂ ≠ p₃) :
  ∡ p₁ s.center p₃ = (2 : ℤ) • ∡ p₁ p₂ p₃ :=
begin
  rw [mem_sphere, @dist_eq_norm_vsub V] at hp₁ hp₂ hp₃,
  rw [oangle, oangle, (o).oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real _ _ hp₂ hp₁ hp₃];
    simp [hp₂p₁, hp₂p₃]
end

/-- Oriented angle version of "angles in same segment are equal" and "opposite angles of a
cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same result),
represented here as equality of twice the angles. -/
lemma two_zsmul_oangle_eq {s : sphere P} {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s)
  (hp₃ : p₃ ∈ s) (hp₄ : p₄ ∈ s) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₄ : p₂ ≠ p₄) (hp₃p₁ : p₃ ≠ p₁)
  (hp₃p₄ : p₃ ≠ p₄) : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄ :=
begin
  rw [mem_sphere, @dist_eq_norm_vsub V] at hp₁ hp₂ hp₃ hp₄,
  rw [oangle, oangle, ←vsub_sub_vsub_cancel_right p₁ p₂ s.center,
      ←vsub_sub_vsub_cancel_right p₄ p₂ s.center,
      (o).two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq _ _ _ _ hp₂ hp₃ hp₁ hp₄];
    simp [hp₂p₁, hp₂p₄, hp₃p₁, hp₃p₄]
end

end sphere

/-- Oriented angle version of "angles in same segment are equal" and "opposite angles of a
cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same result),
represented here as equality of twice the angles. -/
lemma cospherical.two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ : P}
  (h : cospherical ({p₁, p₂, p₃, p₄} : set P)) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₄ : p₂ ≠ p₄)
  (hp₃p₁ : p₃ ≠ p₁) (hp₃p₄ : p₃ ≠ p₄) : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄ :=
begin
  obtain ⟨s, hs⟩ := cospherical_iff_exists_sphere.1 h,
  simp_rw [set.insert_subset, set.singleton_subset_iff, sphere.mem_coe] at hs,
  exact sphere.two_zsmul_oangle_eq hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hp₂p₁ hp₂p₄ hp₃p₁ hp₃p₄
end

namespace sphere

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
angle-at-point form where the apex is given as the center of a circle. -/
lemma oangle_eq_pi_sub_two_zsmul_oangle_center_left {s : sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
  (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) : ∡ p₁ s.center p₂ = π - (2 : ℤ) • ∡ s.center p₂ p₁ :=
by rw [oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq h.symm
  (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)]

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
angle-at-point form where the apex is given as the center of a circle. -/
lemma oangle_eq_pi_sub_two_zsmul_oangle_center_right {s : sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
  (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) : ∡ p₁ s.center p₂ = π - (2 : ℤ) • ∡ p₂ p₁ s.center :=
by rw [oangle_eq_pi_sub_two_zsmul_oangle_center_left hp₁ hp₂ h,
       oangle_eq_oangle_of_dist_eq (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)]

/-- Twice a base angle of an isosceles triangle with apex at the center of a circle, plus twice
the angle at the apex of a triangle with the same base but apex on the circle, equals `π`. -/
lemma two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi {s : sphere P} {p₁ p₂ p₃ : P}
  (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₃ : p₂ ≠ p₃)
  (hp₁p₃ : p₁ ≠ p₃) : (2 : ℤ) • ∡ p₃ p₁ s.center + (2 : ℤ) • ∡ p₁ p₂ p₃ = π :=
by rw [←oangle_center_eq_two_zsmul_oangle hp₁ hp₂ hp₃ hp₂p₁ hp₂p₃,
       oangle_eq_pi_sub_two_zsmul_oangle_center_right hp₁ hp₃ hp₁p₃, add_sub_cancel'_right]

/-- A base angle of an isosceles triangle with apex at the center of a circle is acute. -/
lemma abs_oangle_center_left_to_real_lt_pi_div_two {s : sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
  (hp₂ : p₂ ∈ s) : |(∡ s.center p₂ p₁).to_real| < π / 2 :=
abs_oangle_right_to_real_lt_pi_div_two_of_dist_eq
  (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)

/-- A base angle of an isosceles triangle with apex at the center of a circle is acute. -/
lemma abs_oangle_center_right_to_real_lt_pi_div_two {s : sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
  (hp₂ : p₂ ∈ s) : |(∡ p₂ p₁ s.center).to_real| < π / 2 :=
abs_oangle_left_to_real_lt_pi_div_two_of_dist_eq
  (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)

/-- Given two points on a circle, the center of that circle may be expressed explicitly as a
multiple (by half the tangent of the angle between the chord and the radius at one of those
points) of a `π / 2` rotation of the vector between those points, plus the midpoint of those
points. -/
lemma tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center {s : sphere P} {p₁ p₂ : P}
  (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) :
  (real.angle.tan (∡ p₂ p₁ s.center) / 2) • ((o).rotation (π / 2 : ℝ) (p₂ -ᵥ p₁)) +ᵥ
    midpoint ℝ p₁ p₂ = s.center :=
begin
  obtain ⟨r, hr⟩ := (dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint h).1
    (dist_center_eq_dist_center_of_mem_sphere hp₁ hp₂),
  rw [←hr, ←oangle_midpoint_rev_left, oangle, vadd_vsub_assoc],
  nth_rewrite 0 (show p₂ -ᵥ p₁ = (2 : ℝ) • (midpoint ℝ p₁ p₂ -ᵥ p₁), by simp),
  rw [map_smul, smul_smul, add_comm, (o).tan_oangle_add_right_smul_rotation_pi_div_two,
      mul_div_cancel _ (two_ne_zero' ℝ)],
  simpa using h.symm
end

/-- Given three points on a circle, the center of that circle may be expressed explicitly as a
multiple (by half the inverse of the tangent of the angle at one of those points) of a `π / 2`
rotation of the vector between the other two points, plus the midpoint of those points. -/
lemma inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center {s : sphere P}
  {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) (hp₁p₃ : p₁ ≠ p₃)
  (hp₂p₃ : p₂ ≠ p₃) :
  ((real.angle.tan (∡ p₁ p₂ p₃))⁻¹ / 2) • ((o).rotation (π / 2 : ℝ) (p₃ -ᵥ p₁)) +ᵥ
    midpoint ℝ p₁ p₃ = s.center :=
begin
  convert tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center hp₁ hp₃ hp₁p₃,
  convert (real.angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi _).symm,
  rw [add_comm,
      two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi hp₁ hp₂ hp₃ hp₁p₂.symm hp₂p₃ hp₁p₃]
end

/-- Given two points on a circle, the radius of that circle may be expressed explicitly as half
the distance between those two points divided by the cosine of the angle between the chord and
the radius at one of those points. -/
lemma dist_div_cos_oangle_center_div_two_eq_radius {s : sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
  (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) : dist p₁ p₂ / real.angle.cos (∡ p₂ p₁ s.center) / 2 = s.radius :=
begin
  rw [div_right_comm, div_eq_mul_inv _ (2 : ℝ), mul_comm,
      (show (2 : ℝ)⁻¹ * dist p₁ p₂ = dist p₁ (midpoint ℝ p₁ p₂), by simp), ←mem_sphere.1 hp₁,
      ←tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center hp₁ hp₂ h,
      ←oangle_midpoint_rev_left, oangle, vadd_vsub_assoc,
      (show p₂ -ᵥ p₁ = (2 : ℝ) • (midpoint ℝ p₁ p₂ -ᵥ p₁), by simp), map_smul, smul_smul,
      div_mul_cancel _ (two_ne_zero' ℝ), @dist_eq_norm_vsub' V, @dist_eq_norm_vsub' V,
      vadd_vsub_assoc, add_comm, (o).oangle_add_right_smul_rotation_pi_div_two,
      real.angle.cos_coe, real.cos_arctan, one_div, div_inv_eq_mul,
      ←mul_self_inj (mul_nonneg (norm_nonneg _) (real.sqrt_nonneg _)) (norm_nonneg _),
      norm_add_sq_eq_norm_sq_add_norm_sq_real ((o).inner_smul_rotation_pi_div_two_right _ _),
      ←mul_assoc, mul_comm, mul_comm _ (real.sqrt _), ←mul_assoc, ←mul_assoc,
      real.mul_self_sqrt (add_nonneg zero_le_one (sq_nonneg _)), norm_smul,
      linear_isometry_equiv.norm_map],
  swap, { simpa using h.symm },
  conv_rhs { rw [←mul_assoc, mul_comm _ ‖real.angle.tan _‖, ←mul_assoc, real.norm_eq_abs,
                 abs_mul_abs_self] },
  ring
end

/-- Given two points on a circle, twice the radius of that circle may be expressed explicitly as
the distance between those two points divided by the cosine of the angle between the chord and
the radius at one of those points. -/
lemma dist_div_cos_oangle_center_eq_two_mul_radius {s : sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
  (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) : dist p₁ p₂ / real.angle.cos (∡ p₂ p₁ s.center) = 2 * s.radius :=
by rw [←dist_div_cos_oangle_center_div_two_eq_radius hp₁ hp₂ h,
       mul_div_cancel' _ (two_ne_zero' ℝ)]

/-- Given three points on a circle, the radius of that circle may be expressed explicitly as half
the distance between two of those points divided by the absolute value of the sine of the angle
at the third point (a version of the law of sines or sine rule). -/
lemma dist_div_sin_oangle_div_two_eq_radius {s : sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s)
  (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) (hp₁p₃ : p₁ ≠ p₃) (hp₂p₃ : p₂ ≠ p₃) :
  dist p₁ p₃ / |real.angle.sin (∡ p₁ p₂ p₃)| / 2 = s.radius :=
begin
  convert dist_div_cos_oangle_center_div_two_eq_radius hp₁ hp₃ hp₁p₃,
  rw [←real.angle.abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi
        (two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
          hp₁ hp₂ hp₃ hp₁p₂.symm hp₂p₃ hp₁p₃),
      _root_.abs_of_nonneg (real.angle.cos_nonneg_iff_abs_to_real_le_pi_div_two.2 _)],
  exact (abs_oangle_center_right_to_real_lt_pi_div_two hp₁ hp₃).le
end

/-- Given three points on a circle, twice the radius of that circle may be expressed explicitly as
the distance between two of those points divided by the absolute value of the sine of the angle
at the third point (a version of the law of sines or sine rule). -/
lemma dist_div_sin_oangle_eq_two_mul_radius {s : sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s)
  (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) (hp₁p₃ : p₁ ≠ p₃) (hp₂p₃ : p₂ ≠ p₃) :
  dist p₁ p₃ / |real.angle.sin (∡ p₁ p₂ p₃)| = 2 * s.radius :=
by rw [←dist_div_sin_oangle_div_two_eq_radius hp₁ hp₂ hp₃ hp₁p₂ hp₁p₃ hp₂p₃,
       mul_div_cancel' _ (two_ne_zero' ℝ)]

end sphere

end euclidean_geometry

namespace affine
namespace triangle

open euclidean_geometry

variables {V : Type*} {P : Type*}
  [normed_add_comm_group V] [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P]
  [hd2 : fact (finrank ℝ V = 2)] [module.oriented ℝ V (fin 2)]
include hd2

local notation `o` := module.oriented.positive_orientation

/-- The circumcenter of a triangle may be expressed explicitly as a multiple (by half the inverse
of the tangent of the angle at one of the vertices) of a `π / 2` rotation of the vector between
the other two vertices, plus the midpoint of those vertices. -/
lemma inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter (t : triangle ℝ P)
  {i₁ i₂ i₃ : fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
  ((real.angle.tan (∡ (t.points i₁) (t.points i₂) (t.points i₃)))⁻¹ / 2) •
    ((o).rotation (π / 2 : ℝ) (t.points i₃ -ᵥ t.points i₁)) +ᵥ
    midpoint ℝ (t.points i₁) (t.points i₃) = t.circumcenter :=
sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
  (t.mem_circumsphere _) (t.mem_circumsphere _) (t.mem_circumsphere _)
  (t.independent.injective.ne h₁₂) (t.independent.injective.ne h₁₃) (t.independent.injective.ne h₂₃)

/-- The circumradius of a triangle may be expressed explicitly as half the length of a side
divided by the absolute value of the sine of the angle at the third point (a version of the law
of sines or sine rule). -/
lemma dist_div_sin_oangle_div_two_eq_circumradius (t : triangle ℝ P) {i₁ i₂ i₃ : fin 3}
  (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
  dist (t.points i₁) (t.points i₃) /
    |real.angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))| / 2 = t.circumradius :=
sphere.dist_div_sin_oangle_div_two_eq_radius (t.mem_circumsphere _) (t.mem_circumsphere _)
  (t.mem_circumsphere _) (t.independent.injective.ne h₁₂) (t.independent.injective.ne h₁₃)
  (t.independent.injective.ne h₂₃)

/-- Twice the circumradius of a triangle may be expressed explicitly as the length of a side
divided by the absolute value of the sine of the angle at the third point (a version of the law
of sines or sine rule). -/
lemma dist_div_sin_oangle_eq_two_mul_circumradius (t : triangle ℝ P) {i₁ i₂ i₃ : fin 3}
  (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
  dist (t.points i₁) (t.points i₃) /
    |real.angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))| = 2 * t.circumradius :=
sphere.dist_div_sin_oangle_eq_two_mul_radius (t.mem_circumsphere _) (t.mem_circumsphere _)
  (t.mem_circumsphere _) (t.independent.injective.ne h₁₂) (t.independent.injective.ne h₁₃)
  (t.independent.injective.ne h₂₃)

/-- The circumsphere of a triangle may be expressed explicitly in terms of two points and the
angle at the third point. -/
lemma circumsphere_eq_of_dist_of_oangle (t : triangle ℝ P) {i₁ i₂ i₃ : fin 3} (h₁₂ : i₁ ≠ i₂)
  (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
  t.circumsphere = ⟨((real.angle.tan (∡ (t.points i₁) (t.points i₂) (t.points i₃)))⁻¹ / 2) •
      ((o).rotation (π / 2 : ℝ) (t.points i₃ -ᵥ t.points i₁)) +ᵥ
      midpoint ℝ (t.points i₁) (t.points i₃),
    dist (t.points i₁) (t.points i₃) /
      |real.angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))| / 2⟩ :=
t.circumsphere.ext _
  (t.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter h₁₂ h₁₃ h₂₃).symm
  (t.dist_div_sin_oangle_div_two_eq_circumradius h₁₂ h₁₃ h₂₃).symm

/-- If two triangles have two points the same, and twice the angle at the third point the same,
they have the same circumsphere. -/
lemma circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq {t₁ t₂ : triangle ℝ P}
  {i₁ i₂ i₃ : fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
  (h₁ : t₁.points i₁ = t₂.points i₁) (h₃ : t₁.points i₃ = t₂.points i₃)
  (h₂ : (2 : ℤ) • ∡ (t₁.points i₁) (t₁.points i₂) (t₁.points i₃) =
    (2 : ℤ) • ∡ (t₂.points i₁) (t₂.points i₂) (t₂.points i₃)) :
  t₁.circumsphere = t₂.circumsphere :=
begin
  rw [t₁.circumsphere_eq_of_dist_of_oangle h₁₂ h₁₃ h₂₃,
      t₂.circumsphere_eq_of_dist_of_oangle h₁₂ h₁₃ h₂₃],
  congrm ⟨((_ : ℝ)⁻¹ / 2) • _ +ᵥ _, _ / _ / 2⟩,
  { exact real.angle.tan_eq_of_two_zsmul_eq h₂ },
  { rw [h₁, h₃] },
  { rw [h₁, h₃] },
  { rw [h₁, h₃] },
  { exact real.angle.abs_sin_eq_of_two_zsmul_eq h₂ }
end

/-- Given a triangle, and a fourth point such that twice the angle between two points of the
triangle at that fourth point equals twice the third angle of the triangle, the fourth point
lies in the circumsphere of the triangle. -/
lemma mem_circumsphere_of_two_zsmul_oangle_eq {t : triangle ℝ P} {p : P} {i₁ i₂ i₃ : fin 3}
  (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
  (h : (2 : ℤ) • ∡ (t.points i₁) p (t.points i₃) =
    (2 : ℤ) • ∡ (t.points i₁) (t.points i₂) (t.points i₃)) : p ∈ t.circumsphere :=
begin
  let t'p : fin 3 → P := function.update t.points i₂ p,
  have h₁ : t'p i₁ = t.points i₁, { simp [t'p, h₁₂] },
  have h₂ : t'p i₂ = p, { simp [t'p] },
  have h₃ : t'p i₃ = t.points i₃, { simp [t'p, h₂₃.symm] },
  have ha : affine_independent ℝ t'p,
  { rw [affine_independent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃, h₁, h₂, h₃,
        collinear_iff_of_two_zsmul_oangle_eq h,
        ←affine_independent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃],
    exact t.independent },
  let t' : triangle ℝ P := ⟨t'p, ha⟩,
  have h₁' : t'.points i₁ = t.points i₁ := h₁,
  have h₂' : t'.points i₂ = p := h₂,
  have h₃' : t'.points i₃ = t.points i₃ := h₃,
  have h' : (2 : ℤ) • ∡ (t'.points i₁) (t'.points i₂) (t'.points i₃) =
    (2 : ℤ) • ∡ (t.points i₁) (t.points i₂) (t.points i₃), { rwa [h₁', h₂', h₃'] },
  rw [←circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ h₁' h₃' h',
      ←h₂'],
  exact simplex.mem_circumsphere _ _
end

end triangle
end affine

namespace euclidean_geometry

variables {V : Type*} {P : Type*}
  [normed_add_comm_group V] [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P]
  [hd2 : fact (finrank ℝ V = 2)] [module.oriented ℝ V (fin 2)]
include hd2

local notation `o` := module.oriented.positive_orientation

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π. -/
lemma cospherical_of_two_zsmul_oangle_eq_of_not_collinear {p₁ p₂ p₃ p₄ : P}
  (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) (hn : ¬collinear ℝ ({p₁, p₂, p₄} : set P)) :
  cospherical ({p₁, p₂, p₃, p₄} : set P) :=
begin
  have hn' : ¬collinear ℝ ({p₁, p₃, p₄} : set P), { rwa ←collinear_iff_of_two_zsmul_oangle_eq h },
  let t₁ : affine.triangle ℝ P := ⟨![p₁, p₂, p₄], affine_independent_iff_not_collinear_set.2 hn⟩,
  let t₂ : affine.triangle ℝ P := ⟨![p₁, p₃, p₄], affine_independent_iff_not_collinear_set.2 hn'⟩,
  rw cospherical_iff_exists_sphere,
  refine ⟨t₂.circumsphere, _⟩,
  simp_rw [set.insert_subset, set.singleton_subset_iff],
  refine ⟨t₂.mem_circumsphere 0, _, t₂.mem_circumsphere 1, t₂.mem_circumsphere 2⟩,
  rw affine.triangle.circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq
    (dec_trivial : (0 : fin 3) ≠ 1) (dec_trivial: (0 : fin 3) ≠ 2) dec_trivial
    (show t₂.points 0 = t₁.points 0, from rfl) rfl h.symm,
  exact t₁.mem_circumsphere 1
end

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π, with a "concyclic" conclusion. -/
lemma concyclic_of_two_zsmul_oangle_eq_of_not_collinear {p₁ p₂ p₃ p₄ : P}
  (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) (hn : ¬collinear ℝ ({p₁, p₂, p₄} : set P)) :
  concyclic ({p₁, p₂, p₃, p₄} : set P) :=
⟨cospherical_of_two_zsmul_oangle_eq_of_not_collinear h hn, coplanar_of_fact_finrank_eq_two _⟩

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π, with a "cospherical or collinear" conclusion. -/
lemma cospherical_or_collinear_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ : P}
  (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) :
  cospherical ({p₁, p₂, p₃, p₄} : set P) ∨ collinear ℝ ({p₁, p₂, p₃, p₄} : set P) :=
begin
  by_cases hc : collinear ℝ ({p₁, p₂, p₄} : set P),
  { by_cases he : p₁ = p₄,
    { rw [he, set.insert_eq_self.2 (set.mem_insert_of_mem _ (set.mem_insert_of_mem _
            (set.mem_singleton _)))],
      by_cases hl : collinear ℝ ({p₂, p₃, p₄} : set P), { exact or.inr hl },
      rw or_iff_left hl,
      let t : affine.triangle ℝ P := ⟨![p₂, p₃, p₄], affine_independent_iff_not_collinear_set.2 hl⟩,
      rw cospherical_iff_exists_sphere,
      refine ⟨t.circumsphere, _⟩,
      simp_rw [set.insert_subset, set.singleton_subset_iff],
      exact ⟨t.mem_circumsphere 0, t.mem_circumsphere 1, t.mem_circumsphere 2⟩ },
    have hc' : collinear ℝ ({p₁, p₃, p₄} : set P),
    { rwa [←collinear_iff_of_two_zsmul_oangle_eq h] },
    refine or.inr _,
    rw set.insert_comm p₁ p₂ at hc,
    rwa [set.insert_comm p₁ p₂, hc'.collinear_insert_iff_of_ne (set.mem_insert _ _)
           (set.mem_insert_of_mem _ (set.mem_insert_of_mem _ (set.mem_singleton _))) he] },
  { exact or.inl (cospherical_of_two_zsmul_oangle_eq_of_not_collinear h hc) }
end

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π, with a "concyclic or collinear" conclusion. -/
lemma concyclic_or_collinear_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ : P}
  (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) :
  concyclic ({p₁, p₂, p₃, p₄} : set P) ∨ collinear ℝ ({p₁, p₂, p₃, p₄} : set P) :=
begin
  rcases cospherical_or_collinear_of_two_zsmul_oangle_eq h with hc | hc,
  { exact or.inl ⟨hc, coplanar_of_fact_finrank_eq_two _⟩ },
  { exact or.inr hc }
end

end euclidean_geometry
