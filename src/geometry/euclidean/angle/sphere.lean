/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import geometry.euclidean.angle.oriented.basic

/-!
# Angles in circles and sphere.

This file proves results about angles in circles and spheres.

-/

noncomputable theory

open finite_dimensional complex
open_locale real real_inner_product_space complex_conjugate

namespace orientation

variables {V : Type*} [inner_product_space ℝ V]
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
