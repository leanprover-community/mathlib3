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
* `nat.succ_mul_central_binom_succ`: the inductive relationship between successive central binomial
  coefficients.
* `nat.four_pow_lt_mul_central_binom`: an exponential lower bound on the central binomial
  coefficient.
-/

namespace nat

/--
The central binomial coefficient, `nat.choose (2 * n) n`.
-/
def central_binom (n : ℕ) := (2 * n).choose n

lemma central_binom_eq_two_mul_choose (n : ℕ) : central_binom n = (2 * n).choose n := rfl

lemma central_binom_pos (n : ℕ) : 0 < central_binom n :=
choose_pos (nat.le_mul_of_pos_left zero_lt_two)

lemma central_binom_ne_zero (n : ℕ) : central_binom n ≠ 0 :=
(central_binom_pos n).ne'

@[simp] lemma central_binom_zero : central_binom 0 = 1 :=
choose_zero_right _

/--
The central binomial coefficient is the largest binomial coefficient.
-/
lemma choose_le_central_binom (r n : ℕ) : choose (2 * n) r ≤ central_binom n :=
calc (2 * n).choose r ≤ (2 * n).choose (2 * n / 2) : choose_le_middle r (2 * n)
... = (2 * n).choose n : by rw nat.mul_div_cancel_left n zero_lt_two

lemma two_le_central_binom (n : ℕ) (n_pos : 0 < n) : 2 ≤ central_binom n :=
calc 2 ≤ 2 * n : le_mul_of_pos_right n_pos
... = (2 * n).choose 1 : (choose_one_right (2 * n)).symm
... ≤ central_binom n : choose_le_central_binom 1 n

/--
An inductive property of the central binomial coefficient.
-/
lemma succ_mul_central_binom_succ (n : ℕ) :
  (n + 1) * central_binom (n + 1) = 2 * (2 * n + 1) * central_binom n :=
calc (n + 1) * (2 * (n + 1)).choose (n + 1) = (2 * n + 2).choose (n + 1) * (n + 1) : mul_comm _ _
... = (2 * n + 1).choose n * (2 * n + 2) : by rw [choose_succ_right_eq, choose_mul_succ_eq]
... = 2 * ((2 * n + 1).choose n * (n + 1)) : by ring
... = 2 * ((2 * n + 1).choose n * ((2 * n + 1) - n)) :
  by rw [two_mul n, add_assoc, nat.add_sub_cancel_left]
... = 2 * ((2 * n).choose n * (2 * n + 1)) : by rw choose_mul_succ_eq
... = (2 * (2 * n + 1)) * (2 * n).choose n : by rw [mul_assoc, mul_comm (2 * n + 1)]

/--
An exponential lower bound on the central binomial coefficient.
This bound is of interest because it appears in
[Tochiori's refinement of Erdős's proof of Bertrand's postulate](https://en.wikipedia.org/w/index.php?title=Proof_of_Bertrand%27s_postulate&oldid=859165151#Proof_by_Shigenori_Tochiori).
-/
lemma four_pow_lt_mul_central_binom (n : ℕ) (n_big : 4 ≤ n) : 4 ^ n < n * central_binom n :=
begin
  induction n using nat.strong_induction_on with n IH,
  rcases lt_trichotomy n 4 with (hn|rfl|hn),
  { clear IH, dec_trivial! },
  { norm_num [central_binom, choose] },
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := nat.exists_eq_succ_of_ne_zero (zero_lt_four.trans hn).ne',
  calc 4 ^ (n + 1) < 4 * (n * central_binom n) :
      (mul_lt_mul_left zero_lt_four).mpr (IH n n.lt_succ_self (nat.le_of_lt_succ hn))
  ... ≤ 2 * (2 * n + 1) * central_binom n : by { rw ← mul_assoc, linarith }
  ... = (n + 1) * central_binom (n + 1) : (succ_mul_central_binom_succ n).symm,
end

/--
An exponential lower bound on the central binomial coefficient.
This bound is weaker than `four_pow_n_lt_n_mul_central_binom`, but it is of historical interest
because it appears in Erdős's proof of Bertrand's postulate.
-/
lemma four_pow_le_two_mul_self_mul_central_binom : ∀ (n : ℕ) (n_pos : 0 < n),
  4 ^ n ≤ (2 * n) * central_binom n
| 0 pr := (nat.not_lt_zero _ pr).elim
| 1 pr := by norm_num [central_binom, choose]
| 2 pr := by norm_num [central_binom, choose]
| 3 pr := by norm_num [central_binom, choose]
| n@(m + 4) _ :=
calc 4 ^ n ≤ n * central_binom n : (four_pow_lt_mul_central_binom _ le_add_self).le
... ≤ 2 * n * central_binom n    : by { rw [mul_assoc], refine le_mul_of_pos_left zero_lt_two }

end nat
