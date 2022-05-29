/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Patrick Stevens, Thomas Browning
-/

import data.nat.choose.central
import number_theory.padics.padic_norm
import data.nat.multiplicity

/-!
# Factorization of Binomial Coefficients

This file contains a few results on the arity of primes within certain size
bounds in binomial coeffcicients, particularly the central binaomial coefficient. These include:

* `nat.factorization_central_binom_le`: a logarithmic upper bound on the multiplicity of a prime in
  the central binomial coefficient.
* `nat.factorization_central_binom_of_large_le_one`: Primes above `sqrt (2 * n)` appear at most once
  in the factorization of the `n`th central binomial coefficient.
* `nat.factorization_central_binom_of_two_mul_self_lt_3_mul_prime`: Primes from `2 * n / 3` to `n`
do not appear in the factorization of the `n`th central binomial coefficient.
* `nat.factorization_central_binom_eq_zero_of_two_mul_lt_prime`: Primes greater than `2 * n` do not
  appear in the factorization of the `n`th central binomial coefficient.

These results appear in the [Erdős proof of Bertrand's postulate](aigner1999proofs).
-/

namespace nat

variables {p n : ℕ}

/--
A logarithmic upper bound on the multiplicity of a prime in the central binomial coefficient.
-/
lemma factorization_central_binom_le (hp : p.prime) :
  ((central_binom n).factorization p) ≤ log p (2 * n) :=
begin
  rw ←@padic_val_nat_eq_factorization p (central_binom n) ⟨hp⟩,
  rw @padic_val_nat_def _ ⟨hp⟩ _ (central_binom_pos n),
  unfold central_binom,
  have two_mul_sub : 2 * n - n = n, by rw [two_mul n, nat.add_sub_cancel n n],
  simp only [nat.prime.multiplicity_choose hp (le_mul_of_pos_left zero_lt_two) (lt_add_one _),
      two_mul_sub, ←two_mul, enat.get_coe', finset.filter_congr_decidable],
  calc _  ≤ (finset.Ico 1 (log p (2 * n) + 1)).card : finset.card_filter_le _ _
      ... = (log p (2 * n) + 1) - 1                 : nat.card_Ico _ _,
end

/--
A `pow` form of `nat.factorization_central_binom_le`
-/
lemma pow_factorization_central_binom_le_two_mul {p n : ℕ} (hp : p.prime) (n_pos : 0 < n) :
  p ^ ((central_binom n).factorization p) ≤ 2 * n :=
(pow_le_pow hp.one_lt.le (factorization_central_binom_le hp)).trans
  (pow_log_le_self hp.one_lt (by linarith))

/--
Primes greater than about `sqrt (2 * n)` appear only to multiplicity 0 or 1 in the central binomial
coefficient.
-/
lemma factorization_central_binom_of_large_le_one (hp : p.prime) (p_large : 2 * n < p ^ 2) :
  (((central_binom n).factorization p)) ≤ 1 :=
begin
  have log_weak_bound : log p (2 * n) ≤ 2,
  { calc log p (2 * n) ≤ log p (p ^ 2) : log_monotone (le_of_lt p_large)
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

  exact le_trans (factorization_central_binom_le hp) log_bound,
end

/--
Primes greater than about `2 * n / 3` and less than `n` do not appear in the factorization of
`central_binom n`.
-/
lemma factorization_central_binom_of_two_mul_self_lt_3_mul_prime
  (hp : p.prime) (n_big : 2 < n) (p_le_n : p ≤ n) (big : 2 * n < 3 * p) :
  ((central_binom n).factorization p) = 0 :=
begin
  rw ←@padic_val_nat_eq_factorization p (central_binom n) ⟨hp⟩,
  rw @padic_val_nat_def _ ⟨hp⟩ _ (central_binom_pos n),
  unfold central_binom,
  have two_mul_sub : 2 * n - n = n, by rw [two_mul n, nat.add_sub_cancel n n],
  simp only [nat.prime.multiplicity_choose hp (le_mul_of_pos_left zero_lt_two) (lt_add_one _),
    two_mul_sub, ←two_mul, finset.card_eq_zero, enat.get_coe', finset.filter_congr_decidable],
  clear two_mul_sub,

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
    suffices h : 2 * (p * (n / p)) + 2 * (n % p) < 2 * (p * (n / p)) + p,
    { exact (add_lt_add_iff_left (2 * (p * (n / p)))).mp h, },
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

lemma factorization_eq_zero_of_lt (h : n < p) : n.factorization p = 0 :=
finsupp.not_mem_support_iff.mp (mt le_of_mem_factorization (not_le_of_lt h))

lemma factorization_factorial_eq_zero_of_lt_prime (h : n < p) :
  (factorial n).factorization p = 0 :=
begin
  induction n with n hn,
  { rw [factorial_zero, factorization_one, finsupp.coe_zero, pi.zero_apply] },
  rw [factorial_succ, factorization_mul n.succ_ne_zero n.factorial_ne_zero, finsupp.coe_add,
      pi.add_apply, hn (lt_of_succ_lt h), add_zero, factorization_eq_zero_of_lt h],
end

lemma factorization_binom_eq_zero_of_lt_prime (h : n < p) (k : ℕ) :
  (choose n k).factorization p = 0 :=
begin
  by_cases hnk : n < k,
  { rw [choose_eq_zero_of_lt hnk, factorization_zero, finsupp.coe_zero, pi.zero_apply] },
  rw [choose_eq_factorial_div_factorial (le_of_not_lt hnk),
      factorization_div (factorial_mul_factorial_dvd_factorial (le_of_not_lt hnk)),
      finsupp.coe_tsub, pi.sub_apply, factorization_factorial_eq_zero_of_lt_prime h, zero_tsub],
end

/--
If a prime `p` has positive multiplicity in the `n`th central binomial coefficient,
`p` is no more than `2 * n`
-/
lemma factorization_central_binom_eq_zero_of_two_mul_lt_prime (h : 2 * n < p) :
  ((central_binom n).factorization p) = 0 :=
factorization_binom_eq_zero_of_lt_prime h n

/--
Contrapositive form of `nat.factorization_central_binom_eq_zero_of_two_mul_lt_prime`
-/
lemma prime_le_two_mul_of_factorization_central_binom_pos
  (h_pos : 0 < ((central_binom n).factorization p)) : p ≤ 2 * n :=
begin
  by_contra,
  rw pos_iff_ne_zero at h_pos,
  apply h_pos,
  simp only [not_le] at h,
  exact factorization_central_binom_eq_zero_of_two_mul_lt_prime h,
end

end nat
