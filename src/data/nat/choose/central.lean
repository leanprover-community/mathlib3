/-
Copyright (c) 2021 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Thomas Browning
-/

import data.nat.choose.basic
import tactic.linarith

/-!
# Central binomial coefficients

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves properties of the central binomial coefficients (that is, `nat.choose (2 * n) n`).

## Main definition and results

* `nat.central_binom`: the central binomial coefficient, `(2 * n).choose n`.
* `nat.succ_mul_central_binom_succ`: the inductive relationship between successive central binomial
  coefficients.
* `nat.four_pow_lt_mul_central_binom`: an exponential lower bound on the central binomial
  coefficient.
* `succ_dvd_central_binom`: The result that `n+1 ∣ n.central_binom`, ensuring that the explicit
  definition of the Catalan numbers is integer-valued.
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
[Tochiori's refinement of Erdős's proof of Bertrand's postulate](tochiori_bertrand).
-/
lemma four_pow_lt_mul_central_binom (n : ℕ) (n_big : 4 ≤ n) : 4 ^ n < n * central_binom n :=
begin
  induction n using nat.strong_induction_on with n IH,
  rcases lt_trichotomy n 4 with (hn|rfl|hn),
  { clear IH, dec_trivial! },
  { norm_num [central_binom, choose] },
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := nat.exists_eq_succ_of_ne_zero (zero_lt_four.trans hn).ne',
  calc 4 ^ (n + 1) < 4 * (n * central_binom n) :
      (mul_lt_mul_left $ zero_lt_four' ℕ).mpr (IH n n.lt_succ_self (nat.le_of_lt_succ hn))
  ... ≤ 2 * (2 * n + 1) * central_binom n : by { rw ← mul_assoc, linarith }
  ... = (n + 1) * central_binom (n + 1) : (succ_mul_central_binom_succ n).symm,
end

/--
An exponential lower bound on the central binomial coefficient.
This bound is weaker than `nat.four_pow_lt_mul_central_binom`, but it is of historical interest
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

lemma two_dvd_central_binom_succ (n : ℕ) : 2 ∣ central_binom (n + 1) :=
begin
  use (n+1+n).choose n,
  rw [central_binom_eq_two_mul_choose, two_mul, ← add_assoc, choose_succ_succ, choose_symm_add,
      ← two_mul],
end

lemma two_dvd_central_binom_of_one_le {n : ℕ} (h : 0 < n) : 2 ∣ central_binom n :=
begin
  rw ← nat.succ_pred_eq_of_pos h,
  exact two_dvd_central_binom_succ n.pred,
end

/-- A crucial lemma to ensure that Catalan numbers can be defined via their explicit formula
  `catalan n = n.central_binom / (n + 1)`. -/
lemma succ_dvd_central_binom (n : ℕ) : (n + 1) ∣ n.central_binom :=
begin
  have h_s : (n+1).coprime (2*n+1),
  { rw [two_mul,add_assoc, coprime_add_self_right, coprime_self_add_left],
    exact coprime_one_left n },
  apply h_s.dvd_of_dvd_mul_left,
  apply dvd_of_mul_dvd_mul_left zero_lt_two,
  rw [← mul_assoc, ← succ_mul_central_binom_succ, mul_comm],
  exact mul_dvd_mul_left _ (two_dvd_central_binom_succ n),
end

end nat
