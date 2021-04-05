/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/

import analysis.mean_inequalities

/-!
# IMO 2020 Q2

The real numbers `a`, `b`, `c`, `d` are such that `a ≥ b ≥ c ≥ d > 0` and `a + b + c + d = 1`.
Prove that `(a + 2b + 3c + 4d) a^a b^b c^c d^d < 1`.

A solution is to eliminate the powers using weighted AM-GM and replace
`1` by `(a+b+c+d)^3`, leaving a homogeneous inequality that can be
proved in many ways by expanding, rearranging and comparing individual
terms.  The version here using factors such as `a+3b+3c+3d` is from
the official solutions.
-/

open real

theorem imo2020_q2 (a b c d : ℝ) (hd0 : 0 < d) (hdc : d ≤ c) (hcb : c ≤ b) (hba : b ≤ a)
  (h1 : a + b + c + d = 1) :
  (a + 2 * b + 3 * c + 4 * d) * a ^ a * b ^ b * c ^ c * d ^ d < 1 :=
begin
  have hp : a ^ a * b ^ b * c ^ c * d ^ d ≤ a * a + b * b + c * c + d * d,
  by refine geom_mean_le_arith_mean4_weighted _ _ _ _ _ _ _ _ h1; linarith,
  calc  (a + 2 * b + 3 * c + 4 * d) * a ^ a * b ^ b * c ^ c * d ^ d
      = (a + 2 * b + 3 * c + 4 * d) * (a ^ a * b ^ b * c ^ c * d ^ d) : by ac_refl
  ... ≤ (a + 2 * b + 3 * c + 4 * d) * (a * a + b * b + c * c + d * d) :
    mul_le_mul_of_nonneg_left hp (by linarith)
  ... = (a + 2 * b + 3 * c + 4 * d) * (a * a) + (a + 2 * b + 3 * c + 4 * d) * (b * b) +
        (a + 2 * b + 3 * c + 4 * d) * (c * c) + (a + 2 * b + 3 * c + 4 * d) * (d * d) :
    by simp only [mul_add]
  ... ≤ (a + 3 * b + 3 * c + 3 * d) * (a * a) + (3 * a + b + 3 * c + 3 * d) * (b * b) +
        (3 * a + 3 * b + c + 3 * d) * (c * c) + (3 * a + 3 * b + 3 * c + d) * (d * d) :
    by apply_rules [add_le_add]; refine mul_le_mul_of_nonneg_right _ (mul_self_nonneg _); linarith
  ... < (a + 3 * b + 3 * c + 3 * d) * (a * a) + (3 * a + b + 3 * c + 3 * d) * (b * b) +
        (3 * a + 3 * b + c + 3 * d) * (c * c) + (3 * a + 3 * b + 3 * c + d) * (d * d) +
        (6 * a * b * c + 6 * a * b * d + 6 * a * c * d + 6 * b * c * d) :
    lt_add_of_pos_right _ (by apply_rules [add_pos, mul_pos, zero_lt_one]; linarith)
  ... = (a + b + c + d) ^ 3 : by ring
  ... = 1 : by simp [h1]
end
