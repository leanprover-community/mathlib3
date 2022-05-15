/-
Copyright (c) 2021 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Thomas Browning
-/

import data.nat.prime
import data.nat.choose.basic
import data.nat.choose.sum
import data.nat.multiplicity
import number_theory.padics.padic_norm
import tactic.norm_num
import tactic.linarith

/-!
# Central binomial coefficients

This file proves properties of the central binomial coefficients (that is, `nat.choose (2 * n) n`).

## Main definition and results

* `nat.central_binom`: the central binomial coefficient, `(2 * n).choose n`.
* `nat.succ_mul_central_binom_succ`: the inductive relationship between successive central binomial
  coefficients.
* `nat.four_pow_lt_mul_central_binom`: an exponential lower bound on the central binomial
  coefficient.
* `nat.multiplicity_central_binom_le`: a logarithmic upper bound on the multiplicity of a prime in
  the central binomial coefficient.
* `nat.multiplicity_central_binom_of_large_le_one`: sufficiently large primes appear at most once
  in the factorisation of the central binomial coefficient.
* `nat.multiplicity_central_binom_of_large_eq_zero`: sufficiently large primes less than n do not
  appear in the factorisation of the central binomial coefficient.
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

variables {p n : ℕ}

/--
A logarithmic upper bound on the multiplicity of a prime in the central binomial coefficient.
-/
lemma padic_val_nat_central_binom_le (hp : p.prime) :
  padic_val_nat p (central_binom n) ≤ log p (2 * n) :=
begin
  rw @padic_val_nat_def _ ⟨hp⟩ _ (central_binom_pos n),
  unfold central_binom,
  have two_n_sub : 2 * n - n = n, by rw [two_mul n, nat.add_sub_cancel n n],
  simp only [nat.prime.multiplicity_choose hp (le_mul_of_pos_left zero_lt_two) (lt_add_one _),
      two_n_sub, ←two_mul, enat.get_coe', finset.filter_congr_decidable],
  calc _  ≤ (finset.Ico 1 (log p (2 * n) + 1)).card : finset.card_filter_le _ _
      ... = (log p (2 * n) + 1) - 1                 : nat.card_Ico _ _,
end

/--
Sufficiently large primes appear only to multiplicity 0 or 1 in the central binomial coefficient.
-/
lemma padic_val_nat_central_binom_of_large_le_one (hp : p.prime) (p_large : 2 * n < p ^ 2) :
  (padic_val_nat p (central_binom n)) ≤ 1 :=
begin
  have log_weak_bound : log p (2 * n) ≤ 2,
  { calc log p (2 * n) ≤ log p (p ^ 2) : log_mono_right (le_of_lt p_large)
    ... = 2 : log_pow hp.one_lt 2, },

  have log_bound : log p (2 * n) ≤ 1,
  { cases le_or_lt (log p (2 * n)) 1 with log_le lt_log,
    { exact log_le, },
    { have v : log p (2 * n) = 2 := by linarith,
      cases le_or_lt p (2 * n) with h h,
      { exfalso,
        rw [log_of_one_lt_of_le hp.one_lt h, succ_inj', log_eq_one_iff] at v,
        have bad : p ^ 2 ≤ 2 * n,
        { rw pow_two,
          exact (nat.le_div_iff_mul_le _ _ (prime.pos hp)).1 v.2.2, },
        exact lt_irrefl _ (lt_of_le_of_lt bad p_large), },
      { rw log_of_lt h,
        exact zero_le 1, }, }, },

  exact le_trans (padic_val_nat_central_binom_le hp) log_bound,
end

/--
Sufficiently large primes less than `n` do not appear in the factorisation of `central_binom n`.
-/
lemma padic_val_nat_central_binom_of_large_eq_zero
  (hp : p.prime) (n_big : 2 < n) (p_le_n : p ≤ n) (big : 2 * n < 3 * p) :
  padic_val_nat p (central_binom n) = 0 :=
begin
  rw @padic_val_nat_def _ ⟨hp⟩ _ (central_binom_pos n),
  unfold central_binom,
  have two_n_sub : 2 * n - n = n, by rw [two_mul n, nat.add_sub_cancel n n],
  simp only [nat.prime.multiplicity_choose hp (le_mul_of_pos_left zero_lt_two) (lt_add_one _),
    two_n_sub, ←two_mul, finset.card_eq_zero, enat.get_coe', finset.filter_congr_decidable],
  clear two_n_sub,

  have three_lt_p : 3 ≤ p := by linarith,
  have p_pos : 0 < p := nat.prime.pos hp,

  apply finset.filter_false_of_mem,
  intros i i_in_interval,
  rw finset.mem_Ico at i_in_interval,
  refine not_le.mpr _,

  rcases lt_trichotomy 1 i with H|rfl|H,
  { have two_le_i : 2 ≤ i := nat.succ_le_of_lt H,
    have two_n_lt_pow_p_i : 2 * n < p ^ i,
    { calc 2 * n < 3 * p : big
             ... ≤ p * p : (mul_le_mul_right p_pos).2 three_lt_p
             ... = p ^ 2 : (sq _).symm
             ... ≤ p ^ i : nat.pow_le_pow_of_le_right p_pos two_le_i, },
    have n_mod : n % p ^ i = n,
    { apply nat.mod_eq_of_lt,
      calc n ≤ n + n : nat.le.intro rfl
        ... = 2 * n : (two_mul n).symm
        ... < p ^ i : two_n_lt_pow_p_i, },
    rw n_mod,
    exact two_n_lt_pow_p_i, },

  { rw [pow_one],
    suffices h23 : 2 * (p * (n / p)) + 2 * (n % p) < 2 * (p * (n / p)) + p,
    { exact (add_lt_add_iff_left (2 * (p * (n / p)))).mp h23, },
    have n_big : 1 ≤ (n / p) := (nat.le_div_iff_mul_le' p_pos).2 (trans (one_mul _).le p_le_n),
    rw [←mul_add, nat.div_add_mod],
    calc  2 * n < 3 * p : big
            ... = 2 * p + p : nat.succ_mul _ _
            ... ≤ 2 * (p * (n / p)) + p : add_le_add_right ((mul_le_mul_left zero_lt_two).mpr
            $ ((le_mul_iff_one_le_right p_pos).mpr n_big)) _ },

  { have i_zero: i = 0 := nat.le_zero_iff.mp (nat.le_of_lt_succ H),
    rw [i_zero, pow_zero, nat.mod_one, mul_zero],
    exact zero_lt_one, },
end

end nat
