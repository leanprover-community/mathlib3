/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import data.real.basic

/-!
# Real sign function

This file introduces and contains some results about `real.sign` which maps negative
real numbers to -1 and nonnegative numbers to 1.

## Main definitions

 * `real.sign r` is -1 if `r < 0` and 1 otherwise

## Tags

sign function
-/

namespace real

/-- The sign function that maps negative real numbers to -1 and nonnegative numbers to 1. -/
noncomputable
def sign (r : ℝ) : ℝ := if r < 0 then -1 else 1

lemma sign_of_neg {r : ℝ} (hr : r < 0) : sign r = -1 :=
by rw [sign, if_pos hr]

lemma sign_of_not_neg {r : ℝ} (hr : ¬ r < 0) : sign r = 1 :=
by rw [sign, if_neg hr]

lemma sign_of_zero_le {r : ℝ} (hr : 0 ≤ r) : sign r = 1 :=
sign_of_not_neg (not_lt.2 hr)

@[simp]
lemma sign_zero : sign 0 = 1 :=
sign_of_not_neg $ irrefl 0

@[simp]
lemma sign_one : sign 1 = 1 :=
sign_of_not_neg $ by norm_num

lemma sign_apply_eq (r : ℝ) : sign r = -1 ∨ sign r = 1 :=
begin
  by_cases r < 0,
  { exact or.intro_left _ (if_pos h) },
  { exact or.intro_right _ (if_neg h) }
end

lemma sign_neg {r : ℝ} (hr : r ≠ 0) : sign (-r) = - sign r :=
begin
  by_cases r < 0,
  { rw [sign_of_neg h, sign_of_zero_le, neg_neg],
    rw [le_neg, neg_zero],
    exact le_of_lt h },
  { rw [sign_of_not_neg h, sign_of_neg],
    rw [neg_lt, neg_zero],
    exact lt_of_le_of_ne (le_of_not_lt h) hr.symm }
end

lemma sign_mul_nonneg (r : ℝ) : 0 ≤ sign r * r :=
begin
  by_cases r < 0,
  { rw sign_of_neg h,
    exact mul_nonneg_of_nonpos_of_nonpos (by norm_num) (le_of_lt h) },
  { rw [sign_of_not_neg h, one_mul],
    exact not_lt.1 h }
end

lemma sign_mul_pos_of_ne_zero (r : ℝ) (hr : r ≠ 0) : 0 < sign r * r :=
begin
  refine lt_of_le_of_ne (sign_mul_nonneg r) (λ h, _),
  rw zero_eq_mul at h,
  cases sign_apply_eq r with hneg hpos;
  cases h; { linarith <|> exact hr h }
end

@[simp]
lemma inv_sign (r : ℝ) : (sign r)⁻¹ = sign r :=
begin
  cases sign_apply_eq r with h h,
  { rw h, norm_num },
  { rw h, exact inv_one }
end

@[simp]
lemma sign_inv (r : ℝ) : sign r⁻¹ = sign r :=
begin
  by_cases r < 0,
  { rw [sign_of_neg h, sign_of_neg (inv_lt_zero.2 h)] },
  { rw [sign_of_not_neg h, sign_of_zero_le (inv_nonneg.2 $ not_lt.1 h)] }
end

end real
