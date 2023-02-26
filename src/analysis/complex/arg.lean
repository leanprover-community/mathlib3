/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/

import analysis.inner_product_space.basic
import analysis.special_functions.complex.arg

/-!
# Rays in the complex numbers

This file links the definition `same_ray ℝ x y` with the equality of arguments of complex numbers,
the usual way this is considered.

## Main statements

* `complex.same_ray_iff` : Two complex numbers are on the same ray iff one of them is zero, or they
  have the same argument.
* `complex.abs_add_eq/complex.abs_sub_eq`: If two non zero complex numbers have different argument,
  then the triangle inequality becomes strict.

-/

variables {x y : ℂ}

namespace complex

lemma same_ray_iff : same_ray ℝ x y ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg :=
begin
  rcases eq_or_ne x 0 with rfl | hx,
  { simp },
  rcases eq_or_ne y 0 with rfl | hy,
  { simp },
  simp only [hx, hy, false_or, same_ray_iff_norm_smul_eq, arg_eq_arg_iff hx hy],
  field_simp [hx, hy],
  rw [mul_comm, eq_comm]
end

lemma same_ray_iff_arg_div_eq_zero : same_ray ℝ x y ↔ arg (x / y) = 0 :=
begin
  rw [←real.angle.to_real_zero, ←arg_coe_angle_eq_iff_eq_to_real, same_ray_iff],
  by_cases hx : x = 0, { simp [hx] },
  by_cases hy : y = 0, { simp [hy] },
  simp [hx, hy, arg_div_coe_angle, sub_eq_zero]
end

lemma abs_add_eq_iff : (x + y).abs = x.abs + y.abs ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg :=
same_ray_iff_norm_add.symm.trans same_ray_iff

lemma abs_sub_eq_iff : (x - y).abs = |x.abs - y.abs| ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg :=
same_ray_iff_norm_sub.symm.trans same_ray_iff

lemma same_ray_of_arg_eq (h : x.arg = y.arg) : same_ray ℝ x y :=
same_ray_iff.mpr $ or.inr $ or.inr h

lemma abs_add_eq (h : x.arg = y.arg) : (x + y).abs = x.abs + y.abs :=
(same_ray_of_arg_eq h).norm_add

lemma abs_sub_eq (h : x.arg = y.arg) : (x - y).abs = ‖x.abs - y.abs‖ :=
(same_ray_of_arg_eq h).norm_sub

end complex
