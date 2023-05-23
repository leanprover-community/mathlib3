/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.complex.circle
import analysis.special_functions.complex.log

/-!
# Maps on the unit circle

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove some basic lemmas about `exp_map_circle` and the restriction of `complex.arg`
to the unit circle. These two maps define a local equivalence between `circle` and `ℝ`, see
`circle.arg_local_equiv` and `circle.arg_equiv`, that sends the whole circle to `(-π, π]`.
-/

open complex function set
open_locale real

namespace circle

lemma injective_arg : injective (λ z : circle, arg z) :=
λ z w h, subtype.ext $ ext_abs_arg ((abs_coe_circle z).trans (abs_coe_circle w).symm) h

@[simp] lemma arg_eq_arg {z w : circle} : arg z = arg w ↔ z = w := injective_arg.eq_iff

end circle

lemma arg_exp_map_circle {x : ℝ} (h₁ : -π < x) (h₂ : x ≤ π) : arg (exp_map_circle x) = x :=
by rw [exp_map_circle_apply, exp_mul_I, arg_cos_add_sin_mul_I ⟨h₁, h₂⟩]

@[simp] lemma exp_map_circle_arg (z : circle) : exp_map_circle (arg z) = z :=
circle.injective_arg $ arg_exp_map_circle (neg_pi_lt_arg _) (arg_le_pi _)

namespace circle

/-- `complex.arg ∘ coe` and `exp_map_circle` define a local equivalence between `circle and `ℝ` with
`source = set.univ` and `target = set.Ioc (-π) π`. -/
@[simps { fully_applied := ff }]
noncomputable def arg_local_equiv : local_equiv circle ℝ :=
{ to_fun := arg ∘ coe,
  inv_fun := exp_map_circle,
  source := univ,
  target := Ioc (-π) π,
  map_source' := λ z _, ⟨neg_pi_lt_arg _, arg_le_pi _⟩,
  map_target' := maps_to_univ _ _,
  left_inv' := λ z _, exp_map_circle_arg z,
  right_inv' := λ x hx, arg_exp_map_circle hx.1 hx.2 }

/-- `complex.arg` and `exp_map_circle` define an equivalence between `circle and `(-π, π]`. -/
@[simps { fully_applied := ff }]
noncomputable def arg_equiv : circle ≃ Ioc (-π) π :=
{ to_fun := λ z, ⟨arg z, neg_pi_lt_arg _, arg_le_pi _⟩,
  inv_fun := exp_map_circle ∘ coe,
  left_inv := λ z, arg_local_equiv.left_inv trivial,
  right_inv := λ x, subtype.ext $ arg_local_equiv.right_inv x.2 }

end circle

lemma left_inverse_exp_map_circle_arg : left_inverse exp_map_circle (arg ∘ coe) :=
exp_map_circle_arg

lemma inv_on_arg_exp_map_circle : inv_on (arg ∘ coe) exp_map_circle (Ioc (-π) π) univ :=
circle.arg_local_equiv.symm.inv_on

lemma surj_on_exp_map_circle_neg_pi_pi : surj_on exp_map_circle (Ioc (-π) π) univ :=
circle.arg_local_equiv.symm.surj_on

lemma exp_map_circle_eq_exp_map_circle {x y : ℝ} :
  exp_map_circle x = exp_map_circle y ↔ ∃ m : ℤ, x = y + m * (2 * π) :=
begin
  rw [subtype.ext_iff, exp_map_circle_apply, exp_map_circle_apply, exp_eq_exp_iff_exists_int],
  refine exists_congr (λ n, _),
  rw [← mul_assoc, ← add_mul, mul_left_inj' I_ne_zero, ← of_real_one, ← of_real_bit0,
    ← of_real_mul, ← of_real_int_cast, ← of_real_mul, ← of_real_add, of_real_inj]
end

lemma periodic_exp_map_circle : periodic exp_map_circle (2 * π) :=
λ z, exp_map_circle_eq_exp_map_circle.2 ⟨1, by rw [int.cast_one, one_mul]⟩

@[simp] lemma exp_map_circle_two_pi : exp_map_circle (2 * π) = 1 :=
periodic_exp_map_circle.eq.trans exp_map_circle_zero

lemma exp_map_circle_sub_two_pi (x : ℝ) : exp_map_circle (x - 2 * π) = exp_map_circle x :=
periodic_exp_map_circle.sub_eq x

lemma exp_map_circle_add_two_pi (x : ℝ) : exp_map_circle (x + 2 * π) = exp_map_circle x :=
periodic_exp_map_circle x

/-- `exp_map_circle`, applied to a `real.angle`. -/
noncomputable def real.angle.exp_map_circle (θ : real.angle) : circle :=
periodic_exp_map_circle.lift θ

@[simp] lemma real.angle.exp_map_circle_coe (x : ℝ) :
  real.angle.exp_map_circle x = exp_map_circle x :=
rfl

lemma real.angle.coe_exp_map_circle (θ : real.angle) : (θ.exp_map_circle : ℂ) = θ.cos + θ.sin * I :=
begin
  induction θ using real.angle.induction_on,
  simp [complex.exp_mul_I],
end

@[simp] lemma real.angle.exp_map_circle_zero :
  real.angle.exp_map_circle 0 = 1 :=
by rw [←real.angle.coe_zero, real.angle.exp_map_circle_coe, exp_map_circle_zero]

@[simp] lemma real.angle.exp_map_circle_neg (θ : real.angle) :
  real.angle.exp_map_circle (-θ) = (real.angle.exp_map_circle θ)⁻¹ :=
begin
  induction θ using real.angle.induction_on,
  simp_rw [←real.angle.coe_neg, real.angle.exp_map_circle_coe, exp_map_circle_neg]
end

@[simp] lemma real.angle.exp_map_circle_add (θ₁ θ₂ : real.angle) :
  real.angle.exp_map_circle (θ₁ + θ₂) =
    (real.angle.exp_map_circle θ₁) * (real.angle.exp_map_circle θ₂) :=
begin
  induction θ₁ using real.angle.induction_on,
  induction θ₂ using real.angle.induction_on,
  exact exp_map_circle_add θ₁ θ₂
end

@[simp] lemma real.angle.arg_exp_map_circle (θ : real.angle) :
  (arg (real.angle.exp_map_circle θ) : real.angle) = θ :=
begin
  induction θ using real.angle.induction_on,
  rw [real.angle.exp_map_circle_coe, exp_map_circle_apply, exp_mul_I, ←of_real_cos,
      ←of_real_sin, ←real.angle.cos_coe, ←real.angle.sin_coe, arg_cos_add_sin_mul_I_coe_angle]
end
