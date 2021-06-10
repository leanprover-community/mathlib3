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

lemma sign_apply_eq (r : ℝ) : sign r = -1 ∨ sign r = 1 :=
begin
  by_cases r < 0,
  { exact or.intro_left _ (if_pos h) },
  { exact or.intro_right _ (if_neg h) }
end

lemma sign_mul_nonneg (r : ℝ) : 0 ≤ sign r * r :=
begin
  by_cases r < 0,
  { rw [sign, if_pos h],
    exact mul_nonneg_of_nonpos_of_nonpos (by norm_num) (le_of_lt h) },
  { rw [sign, if_neg h, one_mul],
    exact not_lt.1 h }
end

lemma sign_mul_ne_zero_pos (r : ℝ) (hr : r ≠ 0) : 0 < sign r * r :=
begin
  refine lt_of_le_of_ne (sign_mul_nonneg r) (λ h, _),
  rw zero_eq_mul at h,
  cases sign_apply_eq r with hneg hpos;
  cases h; { linarith <|> exact hr h }
end

@[simp]
lemma sign_inv_eq_self (r : ℝ) : (sign r)⁻¹ = sign r :=
begin
  cases sign_apply_eq r with h h,
  { rw h, norm_num },
  { rw h, exact inv_one }
end

end real
