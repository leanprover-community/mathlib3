/-
Copyright (c) 2020 James Arthur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Chris Hughes, Shing Tak Lam
-/
import analysis.special_functions.trigonometric.deriv
import analysis.special_functions.log.basic

/-!
# Inverse of the sinh function

In this file we prove that sinh is bijective and hence has an
inverse, arsinh.

## Main definitions

- `real.arsinh`: The inverse function of `real.sinh`.

- `real.sinh_equiv`, `real.sinh_order_iso`, `real.sinh_homeomorph`: `real.sinh` as an `equiv`,
  `order_iso`, and `homeomorph`, respectively.

## Main Results

- `real.sinh_surjective`: The proof that `real.sinh` is surjective
- `real.sinh_bijective`: The proof `real.sinh` is bijective

- `real.arsinh_injective`: The proof that `real.arsinh` is injective
- `real.arsinh_surjective`: The proof that `real.arsinh` is surjective
- `real.arsinh_bijective`: The proof `real.arsinh` is bijective

## Tags

arsinh, arcsinh, argsinh, asinh, sinh injective, sinh bijective, sinh surjective
-/
noncomputable theory

open function

namespace real

variables {x y : ℝ}

/-- `arsinh` is defined using a logarithm, `arsinh x = log (x + sqrt(1 + x^2))`. -/
@[pp_nodot] def arsinh (x : ℝ) := log (x + sqrt (1 + x^2))

lemma exp_arsinh (x : ℝ) : exp (arsinh x) = x + sqrt (1 + x^2) :=
begin
  apply exp_log,
  rw [← neg_lt_iff_pos_add'],
  calc -x ≤ sqrt (x ^ 2) : le_sqrt_of_sq_le (neg_pow_bit0 _ _).le
  ... < sqrt (1 + x ^ 2) : sqrt_lt_sqrt (sq_nonneg _) (lt_one_add _)
end

@[simp] lemma arsinh_zero : arsinh 0 = 0 := by simp [arsinh]

@[simp] lemma arsinh_neg (x : ℝ) : arsinh (-x) = -arsinh x :=
begin
  rw [← exp_eq_exp, exp_arsinh, exp_neg, exp_arsinh],
  apply eq_inv_of_mul_eq_one_left,
  rw [neg_sq, neg_add_eq_sub, add_comm x, mul_comm, ← sq_sub_sq, sq_sqrt, add_sub_cancel],
  exact add_nonneg zero_le_one (sq_nonneg _)
end

/-- `arsinh` is the right inverse of `sinh`. -/
@[simp] lemma sinh_arsinh (x : ℝ) : sinh (arsinh x) = x :=
by { rw [sinh_eq, ← arsinh_neg, exp_arsinh, exp_arsinh, neg_sq], field_simp }

@[simp] lemma cosh_arsinh (x : ℝ) : cosh (arsinh x) = sqrt (1 + x^2) :=
by rw [← sqrt_sq (cosh_pos _).le, cosh_sq', sinh_arsinh]

/-- `sinh` is surjective, `∀ b, ∃ a, sinh a = b`. In this case, we use `a = arsinh b`. -/
lemma sinh_surjective : surjective sinh := left_inverse.surjective sinh_arsinh

/-- `sinh` is bijective, both injective and surjective. -/
lemma sinh_bijective : bijective sinh := ⟨sinh_injective, sinh_surjective⟩

/-- `arsinh` is the left inverse of `sinh`. -/
@[simp] lemma arsinh_sinh (x : ℝ) : arsinh (sinh x) = x :=
right_inverse_of_injective_of_left_inverse sinh_injective sinh_arsinh x

/-- `real.sinh` as an `equiv`. -/
@[simps] def sinh_equiv : ℝ ≃ ℝ :=
{ to_fun := sinh,
  inv_fun := arsinh,
  left_inv := arsinh_sinh,
  right_inv := sinh_arsinh }

/-- `real.sinh` as an `order_iso`. -/
@[simps] def sinh_order_iso : ℝ ≃o ℝ :=
{ to_equiv := sinh_equiv,
  map_rel_iff' := @sinh_le_sinh }

/-- `real.sinh` as a `homeomorph`. -/
@[simps] def sinh_homeomorph : ℝ ≃ₜ ℝ := sinh_order_iso.to_homeomorph

lemma arsinh_bijective : bijective arsinh := sinh_equiv.symm.bijective
lemma arsinh_injective : injective arsinh := sinh_equiv.symm.injective
lemma arsinh_surjective : surjective arsinh := sinh_equiv.symm.surjective

lemma arsinh_strict_mono : strict_mono arsinh := sinh_order_iso.symm.strict_mono

@[simp] lemma arsinh_inj : arsinh x = arsinh y ↔ x = y := arsinh_injective.eq_iff
@[simp] lemma arsinh_le_arsinh : arsinh x ≤ arsinh y ↔ x ≤ y := sinh_order_iso.symm.le_iff_le
@[simp] lemma arsinh_lt_arsinh : arsinh x < arsinh y ↔ x < y := sinh_order_iso.symm.lt_iff_lt

end real
