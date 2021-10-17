/-
Copyright (c) 2021 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens
-/

import data.nat.choose.basic
import data.nat.choose.sum

/-!
# Central binomial coefficients

This file proves properties of the central binomial coefficients (that is, `nat.choose (2 * n) n`).
-/


open_locale nat
namespace nat

lemma central_binom_ne_zero (n : ℕ) : (2 * n).choose n ≠ 0 :=
(choose_pos (nat.le_mul_of_pos_left zero_lt_two)).ne'

lemma choose_le_central_binom (r n : ℕ) : choose (2 * n) r ≤ choose (2 * n) n :=
begin
  calc (2 * n).choose r ≤ (2 * n).choose (2 * n / 2) : choose_le_middle r (2 * n)
  ... = (2 * n).choose n : by rw nat.mul_div_cancel_left n zero_lt_two
end

lemma two_le_central_binom (n : ℕ) (n_pos : 0 < n) : 2 ≤ (2 * n).choose n :=
begin
  calc 2 ≤ (2 * n).choose 1 :
    begin
      simp only [choose_one_right],
      exact le_mul_of_pos_right n_pos,
    end
   ... ≤ (2 * n).choose n : choose_le_central_binom 1 n
end

lemma two_mul_sub_self (n : ℕ) : 2 * n - n = n :=
begin
  calc 2 * n - n = n + n - n : by rw two_mul
  ... = n : nat.add_sub_cancel n n,
end

lemma two_mul_succ_sub_self (n : ℕ) : 2 * n + 1 - n = n + 1 :=
begin
  calc 2 * n + 1 - n = n + n + 1 - n : by rw two_mul
  ... = n + 1 + n - n : by ring_nf
  ... = n + 1 : (n + 1).add_sub_cancel n
end

lemma central_binom_induction (n : ℕ) :
  (n + 1) * ((2 * (n + 1)).choose (n + 1)) = (2 * (2 * n + 1)) * (2 * n).choose n :=
begin
  calc (n + 1) * ((2 * (n + 1)).choose (n + 1))
      = (n + 1) * (2 * n + 2).choose (n + 1) : by ring_nf
      ... = (n + 1) * ((2 * n + 1).choose n + (2 * n + 1).choose (n + 1)) : by rw choose_succ_succ
      ... = (n + 1) * ((2 * n + 1).choose (n + 1) + (2 * n + 1).choose (n + 1)) :
        by rw choose_symm_half
      ... = 2 * ((2 * n + 1).choose (n + 1) * (n + 1)) : by ring
      ... = 2 * (((2 * n).choose n + (2 * n).choose (n + 1)) * (n + 1)) :
        by rw choose_succ_succ (2 * n) n
      ... = 2 * ((2 * n).choose n * (n + 1) + (2 * n).choose (n + 1) * (n + 1)) : by ring
      ... = 2 * ((2 * n).choose n * (n + 1) + (2 * n).choose n * (2 * n - n)) :
        by rw choose_succ_right_eq (2 * n) n
      ... = 2 * ((2 * n).choose n * (n + 1) + (2 * n).choose n * n) : by rw two_mul_sub_self
      ... = 2 * (2 * n + 1) * (2 * n).choose n : by ring,
end

-- This bound is of interest because it appears in Tochiori's refinement of Erdős's proof
-- of Bertrand's postulate
-- (https://en.wikipedia.org/w/index.php?title=Proof_of_Bertrand%27s_postulate&oldid=859165151#Proof_by_Shigenori_Tochiori)
lemma four_pow_n_lt_n_mul_central_binom : ∀ (n : ℕ) (n_big : 4 ≤ n), 4 ^ n < n * (2 * n).choose n
| 0 pr := by linarith
| 1 pr := by linarith
| 2 pr := by linarith
| 3 pr := by linarith
| 4 _ := by { norm_num, unfold nat.choose, norm_num }
| (m + 5) _ :=
calc 4 ^ (m + 5) < 4 * ((m + 4) * (2 * (m + 4)).choose (m + 4)) :
  (mul_lt_mul_left zero_lt_four).mpr (four_pow_n_lt_n_mul_central_binom (m + 4) le_add_self)
... = (4 * (m + 4)) * (2 * (m + 4)).choose (m + 4) : (mul_assoc _ _ _).symm
... ≤ (2 * (2 * (m + 4) + 1)) * (2 * (m + 4)).choose (m + 4) : by linarith
... = (m + 5) * (2 * (m + 5)).choose (m + 5) : (central_binom_induction (m + 4)).symm

-- This bound is of interest because it appears in Erdős's proof of Bertrand's postulate.
lemma four_pow_le_two_mul_n_mul_central_binom : ∀ (n : ℕ) (n_pos : 0 < n),
  4 ^ n ≤ (2 * n) * (2 * n).choose n
| 0 pr := by linarith
| 1 pr := by norm_num
| 2 pr := by { norm_num, unfold nat.choose, norm_num }
| 3 pr := by { norm_num, unfold nat.choose, norm_num }
| (m + 4) _ :=
calc 4 ^ (m + 4) ≤ (m + 4) * (2 * (m + 4)).choose (m + 4) :
  le_of_lt (four_pow_n_lt_n_mul_central_binom (m + 4) le_add_self)
... ≤ 2 * ((m + 4) * (2 * (m + 4)).choose (m + 4)) : nat.le_mul_of_pos_left zero_lt_two
... = 2 * (m + 4) * (2 * (m + 4)).choose (m + 4) : (mul_assoc _ _ _).symm

end nat
