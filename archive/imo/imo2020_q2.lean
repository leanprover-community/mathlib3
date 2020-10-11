/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
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

theorem imo2020_q2 : ∀ (a b c d : ℝ), 0 < d → d ≤ c → c ≤ b → b ≤ a → a + b + c + d = 1 →
  (a + 2 * b + 3 * c + 4 * d) * a ^ a * b ^ b * c ^ c * d ^ d < 1 :=
begin
  intros a b c d hd0 hcd hbc hab habcd,
  have hc0 : 0 < c, by linarith,
  have hb0 : 0 < b, by linarith,
  have ha0 : 0 < a, by linarith,
  have hd0' := le_of_lt hd0,
  have hc0' := le_of_lt hc0,
  have hb0' := le_of_lt hb0,
  have ha0' := le_of_lt ha0,
  have hp : a ^ a * b ^ b * c ^ c * d ^ d ≤ a * a + b * b + c * c + d * d :=
    real.geom_mean_le_arith_mean4_weighted ha0' hb0' hc0' hd0' ha0' hb0' hc0' hd0' habcd,
  have h6abc : 0 < 6 * a * b * c := mul_pos (mul_pos (mul_pos (by norm_num) ha0) hb0) hc0,
  have h6abd : 0 < 6 * a * b * d := mul_pos (mul_pos (mul_pos (by norm_num) ha0) hb0) hd0,
  have h6acd : 0 < 6 * a * c * d := mul_pos (mul_pos (mul_pos (by norm_num) ha0) hc0) hd0,
  have h6bcd : 0 < 6 * b * c * d := mul_pos (mul_pos (mul_pos (by norm_num) hb0) hc0) hd0,
  have h6 : 0 < 6 * a * b * c + 6 * a * b * d + 6 * a * c * d + 6 * b * c * d :=
    add_pos (add_pos (add_pos h6abc h6abd) h6acd) h6bcd,
  calc (a + 2 * b + 3 * c + 4 * d) * a ^ a * b ^ b * c ^ c * d ^ d
    = (a + 2 * b + 3 * c + 4 * d) * (a ^ a * b ^ b * c ^ c * d ^ d) : by ring
    ... ≤ (a + 2 * b + 3 * c + 4 * d) * (a * a + b * b + c * c + d * d) :
      mul_le_mul_of_nonneg_left hp (by linarith)
    ... = (a + 2 * b + 3 * c + 4 * d) * (a * a) + (a + 2 * b + 3 * c + 4 * d) * (b * b) +
          (a + 2 * b + 3 * c + 4 * d) * (c * c) + (a + 2 * b + 3 * c + 4 * d) * (d * d) : by ring
    ... ≤ (a + 3 * b + 3 * c + 3 * d) * (a * a) + (3 * a + b + 3 * c + 3 * d) * (b * b) +
          (3 * a + 3 * b + c + 3 * d) * (c * c) + (3 * a + 3 * b + 3 * c + d) * (d * d) :
      add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_right (by linarith)
                                                                     (mul_self_nonneg _))
                                         (mul_le_mul_of_nonneg_right (by linarith)
                                                                     (mul_self_nonneg _)))
                             (mul_le_mul_of_nonneg_right (by linarith) (mul_self_nonneg _)))
                 (mul_le_mul_of_nonneg_right (by linarith) (mul_self_nonneg _))
    ... < (a + 3 * b + 3 * c + 3 * d) * (a * a) + (3 * a + b + 3 * c + 3 * d) * (b * b) +
          (3 * a + 3 * b + c + 3 * d) * (c * c) + (3 * a + 3 * b + 3 * c + d) * (d * d) +
          (6 * a * b * c + 6 * a * b * d + 6 * a * c * d + 6 * b * c * d) :
      lt_add_of_pos_right _ h6
    ... = (a + b + c + d) ^ 3 : by ring
    ... = 1 : by simp [habcd]
end
