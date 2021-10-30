/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.complex.circle
import analysis.special_functions.complex.log

/-!
# Maps on the unit circle

In this file we prove some basic lemmas about `exp_map_circle` and the restriction of `complex.arg`
to the unit circle.
-/

open complex function set
open_locale real

namespace circle

lemma injective_arg : injective (λ z : circle, arg z) :=
λ z w h, subtype.ext $ ext_abs_arg ((abs_eq_of_mem_circle z).trans (abs_eq_of_mem_circle w).symm) h

@[simp] lemma arg_eq_arg {z w : circle} : arg z = arg w ↔ z = w := injective_arg.eq_iff

end circle

lemma arg_exp_map_circle {x : ℝ} (h₁ : -π < x) (h₂ : x ≤ π) : arg (exp_map_circle x) = x :=
by rw [exp_map_circle_apply, exp_mul_I, arg_cos_add_sin_mul_I h₁ h₂]

@[simp] lemma exp_map_circle_arg (z : circle) : exp_map_circle (arg z) = z :=
circle.injective_arg $ arg_exp_map_circle (neg_pi_lt_arg _) (arg_le_pi _)

lemma left_inverse_exp_map_circle_arg : left_inverse exp_map_circle (arg ∘ coe) :=
exp_map_circle_arg

lemma inv_on_arg_exp_map_circle : inv_on (arg ∘ coe) exp_map_circle (Ioc (-π) π) univ :=
⟨λ x hx, arg_exp_map_circle hx.1 hx.2, left_inverse_exp_map_circle_arg.left_inv_on _⟩

lemma surj_on_exp_map_circle_neg_pi_pi : surj_on exp_map_circle (Ioc (-π) π) univ :=
λ z hz, ⟨arg z, ⟨neg_pi_lt_arg _, arg_le_pi _⟩, exp_map_circle_arg z⟩

lemma exp_map_circle_eq_exp_map_circle {x y : ℝ} :
  exp_map_circle x = exp_map_circle y ↔ ∃ m : ℤ, x = y + m * (2 * π) :=
begin
  rw [subtype.ext_iff, exp_map_circle_apply, exp_map_circle_apply, exp_eq_exp_iff_exists_int],
  simp only [← mul_assoc, ← add_mul, mul_left_inj' I_ne_zero], norm_cast
end

lemma periodic_exp_map_circle : periodic exp_map_circle (2 * π) :=
λ z, exp_map_circle_eq_exp_map_circle.2 ⟨1, by rw [int.cast_one, one_mul]⟩

@[simp] lemma exp_map_circle_two_pi : exp_map_circle (2 * π) = 1 :=
periodic_exp_map_circle.eq.trans exp_map_circle_zero

lemma exp_map_circle_sub_two_pi (x : ℝ) : exp_map_circle (x - 2 * π) = exp_map_circle x :=
periodic_exp_map_circle.sub_eq x

lemma exp_map_circle_add_two_pi (x : ℝ) : exp_map_circle (x + 2 * π) = exp_map_circle x :=
periodic_exp_map_circle x

lemma surj_on_exp_map_circle_Ioc_add_two_pi (a : ℝ) :
  surj_on exp_map_circle (Ioc a (a + 2 * π)) univ :=
begin
  intros z hz,
  rcases surj_on_exp_map_circle_neg_pi_pi hz with ⟨x, -, rfl⟩,
  rcases periodic_exp_map_circle.exists_mem_Ioc real.two_pi_pos x a with ⟨y, hy, hxy⟩,
  exact ⟨y, hy, hxy.symm⟩
end
