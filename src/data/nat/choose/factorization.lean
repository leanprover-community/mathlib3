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
bounds in binomial coeffcicients. These include:

* `nat.factorization_choose_le`: a logarithmic upper bound on the multiplicity of a prime in
  a binomial coefficient.
* `nat.factorization_choose_le_one`: Primes above `sqrt n` appear at most once
  in the factorization of `n` choose `k`.
* `nat.factorization_central_binom_of_two_mul_self_lt_3_mul_prime`: Primes from `2 * n / 3` to `n`
do not appear in the factorization of the `n`th central binomial coefficient.
* `nat.factorization_choose_eq_zero_of_lt_prime`: Primes greater than `n` do not
  appear in the factorization of `n` choose `k`.

These results appear in the [Erdős proof of Bertrand's postulate](aigner1999proofs).
-/

namespace nat

variables {p n k : ℕ}

/--
A logarithmic upper bound on the multiplicity of a prime in a binomial coefficient.
-/
lemma factorization_choose_le : (choose n k).factorization p ≤ log p n :=
begin
  by_cases h : (choose n k).factorization p = 0,
  { exact (le_of_eq h).trans zero_le' },
  have hp : p.prime := not.imp_symm (choose n k).factorization_eq_zero_of_non_prime h,
  have hkn : k ≤ n,
  { refine le_of_not_lt (λ hnk, h _),
    rw [choose_eq_zero_of_lt hnk, factorization_zero, finsupp.coe_zero, pi.zero_apply] },
  rw [←@padic_val_nat_eq_factorization p _ ⟨hp⟩, @padic_val_nat_def _ ⟨hp⟩ _ (choose_pos hkn)],
  simp only [hp.multiplicity_choose hkn (lt_add_one _), enat.get_coe],
  refine (finset.card_filter_le _ _).trans (le_of_eq (nat.card_Ico _ _)),
end

/--
A `pow` form of `nat.factorization_choose_le`
-/
lemma pow_factorization_choose_le (hn : 0 < n) : p ^ (choose n k).factorization p ≤ n :=
begin
  cases le_or_lt p 1,
  { exact (pow_le_pow_of_le h).trans ((le_of_eq (one_pow _)).trans hn) },
  { exact (pow_le_iff_le_log h hn).mpr factorization_choose_le },
end

/--
Primes greater than about `sqrt n` appear only to multiplicity 0 or 1 in the binomial coefficient.
-/
lemma factorization_choose_le_one (p_large : n < p ^ 2) : (choose n k).factorization p ≤ 1 :=
begin
  apply factorization_choose_le.trans,
  rw [←not_lt, one_lt_iff_ne_zero_and_ne_one, not_and_distrib, not_not, not_not,
      log_eq_zero_iff, log_eq_one_iff, ←sq, and_iff_right p_large, and_comm,
      ←not_lt, ←not_le, ←not_and_distrib, or_comm],
  exact or_not,
end

/--
Primes greater than about `2 * n / 3` and less than `n` do not appear in the factorization of
`central_binom n`.
-/
lemma factorization_central_binom_of_two_mul_self_lt_three_mul_prime
  (n_big : 2 < n) (p_le_n : p ≤ n) (big : 2 * n < 3 * p) :
  ((central_binom n).factorization p) = 0 :=
begin
  by_cases hp : p.prime,
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
  simp [hp],
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

lemma factorization_choose_eq_zero_of_lt_prime (h : n < p) :
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
  (central_binom n).factorization p = 0 :=
factorization_choose_eq_zero_of_lt_prime h

/--
Contrapositive form of `nat.factorization_central_binom_eq_zero_of_two_mul_lt_prime`
-/
lemma prime_le_two_mul_of_factorization_central_binom_pos
  (h_pos : 0 < (central_binom n).factorization p) : p ≤ 2 * n :=
le_of_not_lt (pos_iff_ne_zero.mp h_pos ∘ factorization_central_binom_eq_zero_of_two_mul_lt_prime)

end nat
