/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import geometry.euclidean.angle.oriented.affine
import geometry.euclidean.angle.unoriented.right_angle

/-!
# Oriented angles in right-angled triangles.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic geometrical results about distances and oriented angles in (possibly
degenerate) right-angled triangles in real inner product spaces and Euclidean affine spaces.

-/

noncomputable theory

open_locale euclidean_geometry
open_locale real
open_locale real_inner_product_space

namespace orientation

open finite_dimensional

variables {V : Type*} [normed_add_comm_group V] [inner_product_space ℝ V]
variables [hd2 : fact (finrank ℝ V = 2)] (o : orientation ℝ V (fin 2))
include hd2 o

/-- An angle in a right-angled triangle expressed using `arccos`. -/
lemma oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  o.oangle x (x + y) = real.arccos (‖x‖ / ‖x + y‖) :=
begin
  have hs : (o.oangle x (x + y)).sign = 1,
  { rw [oangle_sign_add_right, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
      inner_product_geometry.angle_add_eq_arccos_of_inner_eq_zero
        (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]
end

/-- An angle in a right-angled triangle expressed using `arccos`. -/
lemma oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  o.oangle (x + y) y = real.arccos (‖y‖ / ‖x + y‖) :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  rw add_comm,
  exact (-o).oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two h
end

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
lemma oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  o.oangle x (x + y) = real.arcsin (‖y‖ / ‖x + y‖) :=
begin
  have hs : (o.oangle x (x + y)).sign = 1,
  { rw [oangle_sign_add_right, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
      inner_product_geometry.angle_add_eq_arcsin_of_inner_eq_zero
        (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
        (or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]
end

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
lemma oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  o.oangle (x + y) y = real.arcsin (‖x‖ / ‖x + y‖) :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  rw add_comm,
  exact (-o).oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two h
end

/-- An angle in a right-angled triangle expressed using `arctan`. -/
lemma oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  o.oangle x (x + y) = real.arctan (‖y‖ / ‖x‖) :=
begin
  have hs : (o.oangle x (x + y)).sign = 1,
  { rw [oangle_sign_add_right, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
      inner_product_geometry.angle_add_eq_arctan_of_inner_eq_zero
        (o.inner_eq_zero_of_oangle_eq_pi_div_two h) (o.left_ne_zero_of_oangle_eq_pi_div_two h)]
end

/-- An angle in a right-angled triangle expressed using `arctan`. -/
lemma oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  o.oangle (x + y) y = real.arctan (‖x‖ / ‖y‖) :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  rw add_comm,
  exact (-o).oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two h
end

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
lemma cos_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  real.angle.cos (o.oangle x (x + y)) = ‖x‖ / ‖x + y‖ :=
begin
  have hs : (o.oangle x (x + y)).sign = 1,
  { rw [oangle_sign_add_right, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.cos_coe,
      inner_product_geometry.cos_angle_add_of_inner_eq_zero
        (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]
end

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
lemma cos_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  real.angle.cos (o.oangle (x + y) y) = ‖y‖ / ‖x + y‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  rw add_comm,
  exact (-o).cos_oangle_add_right_of_oangle_eq_pi_div_two h
end

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
lemma sin_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  real.angle.sin (o.oangle x (x + y)) = ‖y‖ / ‖x + y‖ :=
begin
  have hs : (o.oangle x (x + y)).sign = 1,
  { rw [oangle_sign_add_right, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.sin_coe,
      inner_product_geometry.sin_angle_add_of_inner_eq_zero
        (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
        (or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]
end

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
lemma sin_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  real.angle.sin (o.oangle (x + y) y) = ‖x‖ / ‖x + y‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  rw add_comm,
  exact (-o).sin_oangle_add_right_of_oangle_eq_pi_div_two h
end

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
lemma tan_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  real.angle.tan (o.oangle x (x + y)) = ‖y‖ / ‖x‖ :=
begin
  have hs : (o.oangle x (x + y)).sign = 1,
  { rw [oangle_sign_add_right, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.tan_coe,
      inner_product_geometry.tan_angle_add_of_inner_eq_zero
        (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]
end

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
lemma tan_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  real.angle.tan (o.oangle (x + y) y) = ‖x‖ / ‖y‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  rw add_comm,
  exact (-o).tan_oangle_add_right_of_oangle_eq_pi_div_two h
end

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
lemma cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : real.angle.cos (o.oangle x (x + y)) * ‖x + y‖ = ‖x‖ :=
begin
  have hs : (o.oangle x (x + y)).sign = 1,
  { rw [oangle_sign_add_right, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.cos_coe,
      inner_product_geometry.cos_angle_add_mul_norm_of_inner_eq_zero
        (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]
end

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
lemma cos_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : real.angle.cos (o.oangle (x + y) y) * ‖x + y‖ = ‖y‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  rw add_comm,
  exact (-o).cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h
end

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
lemma sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : real.angle.sin (o.oangle x (x + y)) * ‖x + y‖ = ‖y‖ :=
begin
  have hs : (o.oangle x (x + y)).sign = 1,
  { rw [oangle_sign_add_right, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.sin_coe,
      inner_product_geometry.sin_angle_add_mul_norm_of_inner_eq_zero
        (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]
end

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
lemma sin_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : real.angle.sin (o.oangle (x + y) y) * ‖x + y‖ = ‖x‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  rw add_comm,
  exact (-o).sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h
end

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
lemma tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : real.angle.tan (o.oangle x (x + y)) * ‖x‖ = ‖y‖ :=
begin
  have hs : (o.oangle x (x + y)).sign = 1,
  { rw [oangle_sign_add_right, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.tan_coe,
      inner_product_geometry.tan_angle_add_mul_norm_of_inner_eq_zero
        (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
        (or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]
end

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
lemma tan_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : real.angle.tan (o.oangle (x + y) y) * ‖y‖ = ‖x‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  rw add_comm,
  exact (-o).tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h
end

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
lemma norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / real.angle.cos (o.oangle x (x + y)) = ‖x + y‖ :=
begin
  have hs : (o.oangle x (x + y)).sign = 1,
  { rw [oangle_sign_add_right, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.cos_coe,
      inner_product_geometry.norm_div_cos_angle_add_of_inner_eq_zero
        (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
        (or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]
end

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
lemma norm_div_cos_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / real.angle.cos (o.oangle (x + y) y) = ‖x + y‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  rw add_comm,
  exact (-o).norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two h
end

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
lemma norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / real.angle.sin (o.oangle x (x + y)) = ‖x + y‖ :=
begin
  have hs : (o.oangle x (x + y)).sign = 1,
  { rw [oangle_sign_add_right, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.sin_coe,
      inner_product_geometry.norm_div_sin_angle_add_of_inner_eq_zero
        (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
        (or.inr (o.right_ne_zero_of_oangle_eq_pi_div_two h))]
end

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
lemma norm_div_sin_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / real.angle.sin (o.oangle (x + y) y) = ‖x + y‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  rw add_comm,
  exact (-o).norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two h
end

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
lemma norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / real.angle.tan (o.oangle x (x + y)) = ‖x‖ :=
begin
  have hs : (o.oangle x (x + y)).sign = 1,
  { rw [oangle_sign_add_right, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.tan_coe,
      inner_product_geometry.norm_div_tan_angle_add_of_inner_eq_zero
        (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
        (or.inr (o.right_ne_zero_of_oangle_eq_pi_div_two h))]
end

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
lemma norm_div_tan_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / real.angle.tan (o.oangle (x + y) y) = ‖y‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  rw add_comm,
  exact (-o).norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two h
end

/-- An angle in a right-angled triangle expressed using `arccos`, version subtracting vectors. -/
lemma oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  o.oangle y (y - x) = real.arccos (‖y‖ / ‖y - x‖) :=
begin
  have hs : (o.oangle y (y - x)).sign = 1,
  { rw [oangle_sign_sub_right_swap, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
      inner_product_geometry.angle_sub_eq_arccos_of_inner_eq_zero
        (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]
end

/-- An angle in a right-angled triangle expressed using `arccos`, version subtracting vectors. -/
lemma oangle_sub_left_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  o.oangle (x - y) x = real.arccos (‖x‖ / ‖x - y‖) :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  exact (-o).oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two h
end

/-- An angle in a right-angled triangle expressed using `arcsin`, version subtracting vectors. -/
lemma oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  o.oangle y (y - x) = real.arcsin (‖x‖ / ‖y - x‖) :=
begin
  have hs : (o.oangle y (y - x)).sign = 1,
  { rw [oangle_sign_sub_right_swap, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
      inner_product_geometry.angle_sub_eq_arcsin_of_inner_eq_zero
        (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
        (or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]
end

/-- An angle in a right-angled triangle expressed using `arcsin`, version subtracting vectors. -/
lemma oangle_sub_left_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  o.oangle (x - y) x = real.arcsin (‖y‖ / ‖x - y‖) :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  exact (-o).oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two h
end

/-- An angle in a right-angled triangle expressed using `arctan`, version subtracting vectors. -/
lemma oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  o.oangle y (y - x) = real.arctan (‖x‖ / ‖y‖) :=
begin
  have hs : (o.oangle y (y - x)).sign = 1,
  { rw [oangle_sign_sub_right_swap, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
      inner_product_geometry.angle_sub_eq_arctan_of_inner_eq_zero
        (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
        (o.right_ne_zero_of_oangle_eq_pi_div_two h)]
end

/-- An angle in a right-angled triangle expressed using `arctan`, version subtracting vectors. -/
lemma oangle_sub_left_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  o.oangle (x - y) x = real.arctan (‖y‖ / ‖x‖) :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  exact (-o).oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two h
end

/-- The cosine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
lemma cos_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  real.angle.cos (o.oangle y (y - x)) = ‖y‖ / ‖y - x‖ :=
begin
  have hs : (o.oangle y (y - x)).sign = 1,
  { rw [oangle_sign_sub_right_swap, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.cos_coe,
      inner_product_geometry.cos_angle_sub_of_inner_eq_zero
        (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]
end

/-- The cosine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
lemma cos_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  real.angle.cos (o.oangle (x - y) x) = ‖x‖ / ‖x - y‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  exact (-o).cos_oangle_sub_right_of_oangle_eq_pi_div_two h
end

/-- The sine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
lemma sin_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  real.angle.sin (o.oangle y (y - x)) = ‖x‖ / ‖y - x‖ :=
begin
  have hs : (o.oangle y (y - x)).sign = 1,
  { rw [oangle_sign_sub_right_swap, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.sin_coe,
      inner_product_geometry.sin_angle_sub_of_inner_eq_zero
        (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
        (or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]
end

/-- The sine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
lemma sin_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  real.angle.sin (o.oangle (x - y) x) = ‖y‖ / ‖x - y‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  exact (-o).sin_oangle_sub_right_of_oangle_eq_pi_div_two h
end

/-- The tangent of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
lemma tan_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  real.angle.tan (o.oangle y (y - x)) = ‖x‖ / ‖y‖ :=
begin
  have hs : (o.oangle y (y - x)).sign = 1,
  { rw [oangle_sign_sub_right_swap, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.tan_coe,
      inner_product_geometry.tan_angle_sub_of_inner_eq_zero
        (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]
end

/-- The tangent of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
lemma tan_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
  real.angle.tan (o.oangle (x - y) x) = ‖y‖ / ‖x‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  exact (-o).tan_oangle_sub_right_of_oangle_eq_pi_div_two h
end

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side, version subtracting vectors. -/
lemma cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : real.angle.cos (o.oangle y (y - x)) * ‖y - x‖ = ‖y‖ :=
begin
  have hs : (o.oangle y (y - x)).sign = 1,
  { rw [oangle_sign_sub_right_swap, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.cos_coe,
      inner_product_geometry.cos_angle_sub_mul_norm_of_inner_eq_zero
        (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]
end

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side, version subtracting vectors. -/
lemma cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : real.angle.cos (o.oangle (x - y) x) * ‖x - y‖ = ‖x‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  exact (-o).cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h
end

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side, version subtracting vectors. -/
lemma sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : real.angle.sin (o.oangle y (y - x)) * ‖y - x‖ = ‖x‖ :=
begin
  have hs : (o.oangle y (y - x)).sign = 1,
  { rw [oangle_sign_sub_right_swap, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.sin_coe,
      inner_product_geometry.sin_angle_sub_mul_norm_of_inner_eq_zero
        (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]
end

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side, version subtracting vectors. -/
lemma sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : real.angle.sin (o.oangle (x - y) x) * ‖x - y‖ = ‖y‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  exact (-o).sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h
end

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side, version subtracting vectors. -/
lemma tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : real.angle.tan (o.oangle y (y - x)) * ‖y‖ = ‖x‖ :=
begin
  have hs : (o.oangle y (y - x)).sign = 1,
  { rw [oangle_sign_sub_right_swap, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.tan_coe,
      inner_product_geometry.tan_angle_sub_mul_norm_of_inner_eq_zero
        (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
        (or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]
end

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side, version subtracting vectors. -/
lemma tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : real.angle.tan (o.oangle (x - y) x) * ‖x‖ = ‖y‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  exact (-o).tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h
end

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse, version subtracting vectors. -/
lemma norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / real.angle.cos (o.oangle y (y - x)) = ‖y - x‖ :=
begin
  have hs : (o.oangle y (y - x)).sign = 1,
  { rw [oangle_sign_sub_right_swap, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.cos_coe,
      inner_product_geometry.norm_div_cos_angle_sub_of_inner_eq_zero
        (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
        (or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]
end

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse, version subtracting vectors. -/
lemma norm_div_cos_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / real.angle.cos (o.oangle (x - y) x) = ‖x - y‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  exact (-o).norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two h
end

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse, version subtracting vectors. -/
lemma norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / real.angle.sin (o.oangle y (y - x)) = ‖y - x‖ :=
begin
  have hs : (o.oangle y (y - x)).sign = 1,
  { rw [oangle_sign_sub_right_swap, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.sin_coe,
      inner_product_geometry.norm_div_sin_angle_sub_of_inner_eq_zero
        (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
        (or.inr (o.left_ne_zero_of_oangle_eq_pi_div_two h))]
end

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse, version subtracting vectors. -/
lemma norm_div_sin_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / real.angle.sin (o.oangle (x - y) x) = ‖x - y‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  exact (-o).norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two h
end

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side, version subtracting vectors. -/
lemma norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / real.angle.tan (o.oangle y (y - x)) = ‖y‖ :=
begin
  have hs : (o.oangle y (y - x)).sign = 1,
  { rw [oangle_sign_sub_right_swap, h, real.angle.sign_coe_pi_div_two] },
  rw [o.oangle_eq_angle_of_sign_eq_one hs, real.angle.tan_coe,
      inner_product_geometry.norm_div_tan_angle_sub_of_inner_eq_zero
        (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
        (or.inr (o.left_ne_zero_of_oangle_eq_pi_div_two h))]
end

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side, version subtracting vectors. -/
lemma norm_div_tan_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
  (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / real.angle.tan (o.oangle (x - y) x) = ‖x‖ :=
begin
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj] at h ⊢,
  exact (-o).norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two h
end

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`. -/
lemma oangle_add_right_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
  o.oangle x (x + r • o.rotation (π / 2 : ℝ) x) = real.arctan r :=
begin
  rcases lt_trichotomy r 0 with hr | rfl | hr,
  { have ha : o.oangle x (r • o.rotation (π / 2 : ℝ) x) = -(π / 2 : ℝ),
    { rw [o.oangle_smul_right_of_neg _ _ hr, o.oangle_neg_right h,
          o.oangle_rotation_self_right h, ←sub_eq_zero, add_comm, sub_neg_eq_add,
          ←real.angle.coe_add, ←real.angle.coe_add, add_assoc, add_halves, ←two_mul,
          real.angle.coe_two_pi],
      simpa using h },
    rw [←neg_inj, ←oangle_neg_orientation_eq_neg, neg_neg] at ha,
    rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj, oangle_rev,
        (-o).oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two ha, norm_smul,
        linear_isometry_equiv.norm_map, mul_div_assoc, div_self (norm_ne_zero_iff.2 h), mul_one,
        real.norm_eq_abs, abs_of_neg hr, real.arctan_neg, real.angle.coe_neg, neg_neg] },
  { rw [zero_smul, add_zero, oangle_self, real.arctan_zero, real.angle.coe_zero] },
  { have ha : o.oangle x (r • o.rotation (π / 2 : ℝ) x) = (π / 2 : ℝ),
    { rw [o.oangle_smul_right_of_pos _ _ hr, o.oangle_rotation_self_right h] },
    rw [o.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two ha, norm_smul,
        linear_isometry_equiv.norm_map, mul_div_assoc, div_self (norm_ne_zero_iff.2 h), mul_one,
        real.norm_eq_abs, abs_of_pos hr] }
end

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`. -/
lemma oangle_add_left_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
  o.oangle (x + r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x) = real.arctan r⁻¹ :=
begin
  by_cases hr : r = 0, { simp [hr] },
  rw [←neg_inj, oangle_rev, ←oangle_neg_orientation_eq_neg, neg_inj,
      ←neg_neg ((π / 2 : ℝ) : real.angle), ←rotation_neg_orientation_eq_neg, add_comm],
  have hx : x = r⁻¹ • ((-o).rotation (π / 2 : ℝ) (r • ((-o).rotation (-(π / 2 : ℝ)) x))),
  { simp [hr] },
  nth_rewrite 2 hx,
  refine (-o).oangle_add_right_smul_rotation_pi_div_two _ _,
  simp [hr, h]
end

/-- The tangent of an angle in a right-angled triangle, where one side is a multiple of a
rotation of another by `π / 2`. -/
lemma tan_oangle_add_right_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
  real.angle.tan (o.oangle x (x + r • o.rotation (π / 2 : ℝ) x)) = r :=
by rw [o.oangle_add_right_smul_rotation_pi_div_two h, real.angle.tan_coe, real.tan_arctan]

/-- The tangent of an angle in a right-angled triangle, where one side is a multiple of a
rotation of another by `π / 2`. -/
lemma tan_oangle_add_left_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
  real.angle.tan (o.oangle (x + r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x)) =
    r⁻¹ :=
by rw [o.oangle_add_left_smul_rotation_pi_div_two h, real.angle.tan_coe, real.tan_arctan]

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`, version subtracting vectors. -/
lemma oangle_sub_right_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
  o.oangle (r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x - x) = real.arctan r⁻¹ :=
begin
  by_cases hr : r = 0, { simp [hr] },
  have hx : -x = r⁻¹ • (o.rotation (π / 2 : ℝ) (r • (o.rotation (π / 2 : ℝ) x))),
  { simp [hr, ←real.angle.coe_add] },
  rw [sub_eq_add_neg, hx, o.oangle_add_right_smul_rotation_pi_div_two],
  simpa [hr] using h
end

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`, version subtracting vectors. -/
lemma oangle_sub_left_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
  o.oangle (x - r • o.rotation (π / 2 : ℝ) x) x = real.arctan r :=
begin
  by_cases hr : r = 0, { simp [hr] },
  have hx : x = r⁻¹ • (o.rotation (π / 2 : ℝ) (-(r • (o.rotation (π / 2 : ℝ) x)))),
  { simp [hr, ←real.angle.coe_add] },
  rw [sub_eq_add_neg, add_comm],
  nth_rewrite 2 hx,
  nth_rewrite 1 hx,
  rw [o.oangle_add_left_smul_rotation_pi_div_two, inv_inv],
  simpa [hr] using h
end

end orientation

namespace euclidean_geometry

open finite_dimensional

variables {V : Type*} {P : Type*}
  [normed_add_comm_group V] [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P]
  [hd2 : fact (finrank ℝ V = 2)] [module.oriented ℝ V (fin 2)]
include hd2

/-- An angle in a right-angled triangle expressed using `arccos`. -/
lemma oangle_right_eq_arccos_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  ∡ p₂ p₃ p₁ = real.arccos (dist p₃ p₂ / dist p₁ p₃) :=
begin
  have hs : (∡ p₂ p₃ p₁).sign = 1, { rw [oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs,
      angle_eq_arccos_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
end

/-- An angle in a right-angled triangle expressed using `arccos`. -/
lemma oangle_left_eq_arccos_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  ∡ p₃ p₁ p₂ = real.arccos (dist p₁ p₂ / dist p₁ p₃) :=
begin
  have hs : (∡ p₃ p₁ p₂).sign = 1, { rw [←oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm,
      angle_eq_arccos_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h),
      dist_comm p₁ p₃]
end

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
lemma oangle_right_eq_arcsin_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  ∡ p₂ p₃ p₁ = real.arcsin (dist p₁ p₂ / dist p₁ p₃) :=
begin
  have hs : (∡ p₂ p₃ p₁).sign = 1, { rw [oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs,
      angle_eq_arcsin_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
                                             (or.inl (left_ne_of_oangle_eq_pi_div_two h))]
end

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
lemma oangle_left_eq_arcsin_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  ∡ p₃ p₁ p₂ = real.arcsin (dist p₃ p₂ / dist p₁ p₃) :=
begin
  have hs : (∡ p₃ p₁ p₂).sign = 1, { rw [←oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm,
      angle_eq_arcsin_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
                                             (or.inr (left_ne_of_oangle_eq_pi_div_two h)),
      dist_comm p₁ p₃]
end

/-- An angle in a right-angled triangle expressed using `arctan`. -/
lemma oangle_right_eq_arctan_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  ∡ p₂ p₃ p₁ = real.arctan (dist p₁ p₂ / dist p₃ p₂) :=
begin
  have hs : (∡ p₂ p₃ p₁).sign = 1, { rw [oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs,
      angle_eq_arctan_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
                                             (right_ne_of_oangle_eq_pi_div_two h)]
end

/-- An angle in a right-angled triangle expressed using `arctan`. -/
lemma oangle_left_eq_arctan_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  ∡ p₃ p₁ p₂ = real.arctan (dist p₃ p₂ / dist p₁ p₂) :=
begin
  have hs : (∡ p₃ p₁ p₂).sign = 1, { rw [←oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm,
      angle_eq_arctan_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
                                             (left_ne_of_oangle_eq_pi_div_two h)]
end

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
lemma cos_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  real.angle.cos (∡ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₃ :=
begin
  have hs : (∡ p₂ p₃ p₁).sign = 1, { rw [oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, real.angle.cos_coe,
      cos_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
end

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
lemma cos_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  real.angle.cos (∡ p₃ p₁ p₂) = dist p₁ p₂ / dist p₁ p₃ :=
begin
  have hs : (∡ p₃ p₁ p₂).sign = 1, { rw [←oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, real.angle.cos_coe,
      cos_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h),
      dist_comm p₁ p₃]
end

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
lemma sin_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  real.angle.sin (∡ p₂ p₃ p₁) = dist p₁ p₂ / dist p₁ p₃ :=
begin
  have hs : (∡ p₂ p₃ p₁).sign = 1, { rw [oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, real.angle.sin_coe,
      sin_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
                                       (or.inl (left_ne_of_oangle_eq_pi_div_two h))]
end

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
lemma sin_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  real.angle.sin (∡ p₃ p₁ p₂) = dist p₃ p₂ / dist p₁ p₃ :=
begin
  have hs : (∡ p₃ p₁ p₂).sign = 1, { rw [←oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, real.angle.sin_coe,
      sin_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
                                       (or.inr (left_ne_of_oangle_eq_pi_div_two h)),
      dist_comm p₁ p₃]
end

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
lemma tan_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  real.angle.tan (∡ p₂ p₃ p₁) = dist p₁ p₂ / dist p₃ p₂ :=
begin
  have hs : (∡ p₂ p₃ p₁).sign = 1, { rw [oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, real.angle.tan_coe,
      tan_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
end

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
lemma tan_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  real.angle.tan (∡ p₃ p₁ p₂) = dist p₃ p₂ / dist p₁ p₂ :=
begin
  have hs : (∡ p₃ p₁ p₂).sign = 1, { rw [←oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, real.angle.tan_coe,
      tan_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
end

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
lemma cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  real.angle.cos (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂ :=
begin
  have hs : (∡ p₂ p₃ p₁).sign = 1, { rw [oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, real.angle.cos_coe,
      cos_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
end

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
lemma cos_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  real.angle.cos (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₁ p₂ :=
begin
  have hs : (∡ p₃ p₁ p₂).sign = 1, { rw [←oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, real.angle.cos_coe, dist_comm p₁ p₃,
      cos_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
end

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
lemma sin_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  real.angle.sin (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂ :=
begin
  have hs : (∡ p₂ p₃ p₁).sign = 1, { rw [oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, real.angle.sin_coe,
      sin_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
end

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
lemma sin_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  real.angle.sin (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₃ p₂ :=
begin
  have hs : (∡ p₃ p₁ p₂).sign = 1, { rw [←oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, real.angle.sin_coe, dist_comm p₁ p₃,
      sin_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
end

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
lemma tan_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  real.angle.tan (∡ p₂ p₃ p₁) * dist p₃ p₂ = dist p₁ p₂ :=
begin
  have hs : (∡ p₂ p₃ p₁).sign = 1, { rw [oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, real.angle.tan_coe,
      tan_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
                                                (or.inr (right_ne_of_oangle_eq_pi_div_two h))]
end

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
lemma tan_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  real.angle.tan (∡ p₃ p₁ p₂) * dist p₁ p₂ = dist p₃ p₂ :=
begin
  have hs : (∡ p₃ p₁ p₂).sign = 1, { rw [←oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, real.angle.tan_coe,
      tan_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
                                                (or.inr (left_ne_of_oangle_eq_pi_div_two h))]
end

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
lemma dist_div_cos_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  dist p₃ p₂ / real.angle.cos (∡ p₂ p₃ p₁) = dist p₁ p₃ :=
begin
  have hs : (∡ p₂ p₃ p₁).sign = 1, { rw [oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, real.angle.cos_coe,
      dist_div_cos_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
                                                (or.inr (right_ne_of_oangle_eq_pi_div_two h))]
end

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
lemma dist_div_cos_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  dist p₁ p₂ / real.angle.cos (∡ p₃ p₁ p₂) = dist p₁ p₃ :=
begin
  have hs : (∡ p₃ p₁ p₂).sign = 1, { rw [←oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, real.angle.cos_coe, dist_comm p₁ p₃,
      dist_div_cos_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
                                                (or.inr (left_ne_of_oangle_eq_pi_div_two h))]
end

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
lemma dist_div_sin_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  dist p₁ p₂ / real.angle.sin (∡ p₂ p₃ p₁) = dist p₁ p₃ :=
begin
  have hs : (∡ p₂ p₃ p₁).sign = 1, { rw [oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, real.angle.sin_coe,
      dist_div_sin_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
                                                (or.inl (left_ne_of_oangle_eq_pi_div_two h))]
end

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
lemma dist_div_sin_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  dist p₃ p₂ / real.angle.sin (∡ p₃ p₁ p₂) = dist p₁ p₃ :=
begin
  have hs : (∡ p₃ p₁ p₂).sign = 1, { rw [←oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, real.angle.sin_coe, dist_comm p₁ p₃,
      dist_div_sin_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
                                                (or.inl (right_ne_of_oangle_eq_pi_div_two h))]
end

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
lemma dist_div_tan_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  dist p₁ p₂ / real.angle.tan (∡ p₂ p₃ p₁) = dist p₃ p₂ :=
begin
  have hs : (∡ p₂ p₃ p₁).sign = 1, { rw [oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, real.angle.tan_coe,
      dist_div_tan_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
                                                (or.inl (left_ne_of_oangle_eq_pi_div_two h))]
end

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
lemma dist_div_tan_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  dist p₃ p₂ / real.angle.tan (∡ p₃ p₁ p₂) = dist p₁ p₂ :=
begin
  have hs : (∡ p₃ p₁ p₂).sign = 1, { rw [←oangle_rotate_sign, h, real.angle.sign_coe_pi_div_two] },
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, real.angle.tan_coe,
      dist_div_tan_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
                                                (or.inl (right_ne_of_oangle_eq_pi_div_two h))]
end

end euclidean_geometry
