/-
Copyright (c) 2021 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Thomas Browning
-/

import data.nat.choose.basic
import data.nat.choose.sum

/-!
# Central binomial coefficients

This file proves properties of the central binomial coefficients (that is, `nat.choose (2 * n) n`).

## Main definition and results

* `nat.central_binom`: the central binomial coefficient, `(2 * n).choose n`.
* `nat.central_binom_induction`: the inductive relationship between successive central binomial
  coefficients.
* `nat.four_pow_n_lt_n_mul_central_binom`: an exponential lower bound on the central binomial
  coefficient.
-/

namespace nat

def central_binom (n : ℕ) := (2 * n).choose n

@[simp] lemma central_binom_def (n : ℕ) : central_binom n = (2 * n).choose n := rfl

lemma central_binom_pos (n : ℕ) : 0 < central_binom n :=
choose_pos (nat.le_mul_of_pos_left zero_lt_two)

lemma central_binom_ne_zero (n : ℕ) : central_binom n ≠ 0 :=
(central_binom_pos n).ne'

lemma choose_le_central_binom (r n : ℕ) : choose (2 * n) r ≤ central_binom n :=
calc (2 * n).choose r ≤ (2 * n).choose (2 * n / 2) : choose_le_middle r (2 * n)
... = (2 * n).choose n : by rw nat.mul_div_cancel_left n zero_lt_two

lemma two_le_central_binom (n : ℕ) (n_pos : 0 < n) : 2 ≤ central_binom n :=
calc 2 ≤ 2 * n : le_mul_of_pos_right n_pos
... = (2 * n).choose 1 : (choose_one_right (2 * n)).symm
... ≤ (2 * n).choose n : choose_le_central_binom 1 n

lemma central_binom_induction (n : ℕ) :
  (n + 1) * (central_binom (n + 1)) = (2 * (2 * n + 1)) * central_binom n :=
calc (n + 1) * (2 * (n + 1)).choose (n + 1) = (2 * n + 2).choose (n + 1) * (n + 1) : mul_comm _ _
... = (2 * n + 1).choose n * (2 * n + 2) : by rw [choose_succ_right_eq, choose_mul_succ_eq]
... = 2 * ((2 * n + 1).choose n * (n + 1)) : by ring
... = 2 * ((2 * n + 1).choose n * ((2 * n + 1) - n)) :
  by rw [two_mul n, add_assoc, nat.add_sub_cancel_left]
... = 2 * ((2 * n).choose n * (2 * n + 1)) : by rw choose_mul_succ_eq
... = (2 * (2 * n + 1)) * (2 * n).choose n : by rw [mul_assoc, mul_comm (2 * n + 1)]

-- This bound is of interest because it appears in Tochiori's refinement of Erdős's proof
-- of Bertrand's postulate
-- (https://en.wikipedia.org/w/index.php?title=Proof_of_Bertrand%27s_postulate&oldid=859165151#Proof_by_Shigenori_Tochiori)
lemma four_pow_n_lt_n_mul_central_binom : ∀ (n : ℕ) (n_big : 4 ≤ n), 4 ^ n < n * central_binom n
| 0 n_big := by norm_num at n_big
| 1 n_big := by norm_num at n_big
| 2 n_big := by norm_num at n_big
| 3 n_big := by norm_num at n_big
| 4 n_big := by { norm_num, unfold nat.choose, norm_num }
| (m + 5) n_big :=
calc 4 ^ (m + 5) < 4 * ((m + 4) * central_binom (m + 4)) :
  (mul_lt_mul_left zero_lt_four).mpr (four_pow_n_lt_n_mul_central_binom (m + 4) le_add_self)
... = (4 * (m + 4)) * central_binom (m + 4) : (mul_assoc _ _ _).symm
... ≤ (2 * (2 * (m + 4) + 1)) * central_binom (m + 4) : by linarith
... = (m + 5) * central_binom (m + 5) : (central_binom_induction (m + 4)).symm

-- This bound is of interest because it appears in Erdős's proof of Bertrand's postulate.
lemma four_pow_le_two_mul_n_mul_central_binom : ∀ (n : ℕ) (n_pos : 0 < n),
  4 ^ n ≤ (2 * n) * central_binom n
| 0 pr := by linarith
| 1 pr := by norm_num
| 2 pr := by { norm_num, unfold nat.choose, norm_num }
| 3 pr := by { norm_num, unfold nat.choose, norm_num }
| (m + 4) _ :=
calc 4 ^ (m + 4) ≤ (m + 4) * central_binom (m + 4) :
  le_of_lt (four_pow_n_lt_n_mul_central_binom (m + 4) le_add_self)
... ≤ 2 * ((m + 4) * central_binom (m + 4)) : nat.le_mul_of_pos_left zero_lt_two
... = 2 * (m + 4) * central_binom (m + 4) : (mul_assoc _ _ _).symm

end nat
