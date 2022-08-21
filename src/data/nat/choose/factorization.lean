/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Patrick Stevens, Thomas Browning
-/

import data.nat.choose.central
import data.nat.factorization.basic
import data.nat.factorial.factorization
import data.nat.multiplicity

/-!
# Factorization of Binomial Coefficients

This file contains a few results on the multiplicity of prime factors within certain size
bounds in binomial coefficients. These include:

* `nat.factorization_choose_le_log`: a logarithmic upper bound on the multiplicity of a prime in
  a binomial coefficient.
* `nat.factorization_choose_le_one`: Primes above `sqrt n` appear at most once
  in the factorization of `n` choose `k`.
* `nat.factorization_central_binom_of_two_mul_self_lt_three_mul`: Primes from `2 * n / 3` to `n`
do not appear in the factorization of the `n`th central binomial coefficient.
* `nat.factorization_choose_eq_zero_of_lt`: Primes greater than `n` do not
  appear in the factorization of `n` choose `k`.

These results appear in the [Erdős proof of Bertrand's postulate](aigner1999proofs).
-/

open finset nat --multiplicity
open_locale big_operators nat

namespace nat

variables {p n k : ℕ}

lemma factorization_choose_aux {p n b k : ℕ} (hp : p.prime) (hkn : k ≤ n) :
  ∑ i in finset.Ico 1 b, n / p ^ i =
  ∑ i in finset.Ico 1 b, k / p ^ i + ∑ i in finset.Ico 1 b, (n - k) / p ^ i +
  ((finset.Ico 1 b).filter (λ i, p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card :=
calc ∑ i in finset.Ico 1 b, n / p ^ i
    = ∑ i in finset.Ico 1 b, (k + (n - k)) / p ^ i :
    by simp only [add_tsub_cancel_of_le hkn]
... = ∑ i in finset.Ico 1 b, (k / p ^ i + (n - k) / p ^ i +
      if p ^ i ≤ k % p ^ i + (n - k) % p ^ i then 1 else 0) :
    by simp only [nat.add_div (pow_pos hp.pos _)]
... = _ : by simp [sum_add_distrib, sum_boole]


/-- The multiplicity of `p` in `choose n k` is the number of carries when `k` and `n - k`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound greater than `log p n`. -/
lemma factorization_choose {p n k b : ℕ} (hp : p.prime) (hkn : k ≤ n) (hnb : log p n < b) :
  (choose n k).factorization p =
  ((Ico 1 b).filter (λ i, p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card :=
begin
  have h1 := (choose_pos hkn).ne',
  have h2 : (n.choose k * k! * (n - k)!).factorization p = n!.factorization p,
  { rw choose_mul_factorial_mul_factorial hkn },
  rw [factorization_mul (mul_ne_zero_iff.2 ⟨h1, factorial_ne_zero k⟩) (factorial_ne_zero (n-k)),
      factorization_mul h1 (factorial_ne_zero k)] at h2,
  simp_rw [finsupp.add_apply] at h2,
  rw [←@add_right_cancel_iff _ _ ((k!.factorization) p + ((n - k)!.factorization) p),
      ←add_assoc, h2,
      hp.factorization_factorial'' hnb, factorization_choose_aux hp hkn,
      add_comm, add_right_inj,
      hp.factorization_factorial'' (lt_of_le_of_lt (log_mono_right tsub_le_self) hnb),
      hp.factorization_factorial'' (lt_of_le_of_lt (log_mono_right hkn) hnb)],
end

/-- A lower bound on the multiplicity of `p` in `choose n k`.
Note that this needs more assumptions on `n` and `k` than the corresponding lemma
`multiplicity_le_multiplicity_choose_add`. -/
lemma factorization_le_factorization_choose_add {p : ℕ} (hp : p.prime) :
  ∀ {n k : ℕ}, k ≠ 0 → k ≤ n → n.factorization p ≤ (choose n k).factorization p + k.factorization p
| _     0     := by simp
| 0     (_+1) := by simp
| (n+1) (k+1) := by
  { rintro hk hkn,
    rw [←finsupp.add_apply,
      ←factorization_mul (λ H, not_lt_of_le hkn (choose_eq_zero_iff.1 H)) hk, ←succ_mul_choose_eq],
    have h1 := mul_ne_zero (succ_ne_zero n) ((choose_pos (succ_le_succ_iff.1 hkn)).ne'),
    have h2 := (factorization_le_iff_dvd (succ_ne_zero n) h1).2 (dvd_mul_right (n+1) (n.choose k)),
    exact finsupp.le_def.1 h2 p }

lemma factorization_choose_prime_pow {p n k : ℕ} (hp : p.prime) (hkn : k ≤ p ^ n) (hk0 : 0 < k) :
  (choose (p ^ n) k).factorization p + k.factorization p = n :=
begin
  refine le_antisymm _ _,
  { rw [factorization_choose hp hkn (lt_succ_self _), log_pow hp.one_lt,
        factorization_eq_card_pow_dvd k hp, ←card_disjoint_union],
    swap,
    { simp only [disjoint_right, mem_filter, mem_Ico, not_and, not_le, and_imp],
      rintro a - - h3,
      simp [dvd_iff_mod_eq_zero.1 h3, nat.mod_lt _ (pow_pos hp.pos _)] },
    rw [Ico_filter_pow_dvd_eq hp hk0.ne' hkn, ←Ico_succ_right, filter_union_right],
    refine le_trans ((Ico 1 n.succ).card_filter_le _) _,
    simp },
  { refine le_trans _ (factorization_le_factorization_choose_add hp hk0.ne' hkn),
    simp [hp.factorization_pow] },
end


/--
A logarithmic upper bound on the multiplicity of a prime in a binomial coefficient.
-/
lemma factorization_choose_le_log : (choose n k).factorization p ≤ log p n :=
begin
  by_cases h : (choose n k).factorization p = 0, { simp [h] },
  cases em' p.prime with hp hp, { cases h (factorization_eq_zero_of_non_prime _ hp) },
  rcases lt_or_le n k with hnk | hkn, { simp [choose_eq_zero_of_lt hnk] },
  simp only [hp.factorization_choose hkn (lt_add_one _)],
  apply (finset.card_filter_le _ _).trans,
  simp,
end

/--
A `pow` form of `nat.factorization_choose_le`
-/
lemma pow_factorization_choose_le (hn : 0 < n) : p ^ (choose n k).factorization p ≤ n :=
begin
  cases le_or_lt p 1,
  { exact (pow_le_pow_of_le h).trans ((le_of_eq (one_pow _)).trans hn) },
  { exact (pow_le_iff_le_log h hn).mpr factorization_choose_le_log },
end

/--
Primes greater than about `sqrt n` appear only to multiplicity 0 or 1 in the binomial coefficient.
-/
lemma factorization_choose_le_one (p_large : n < p ^ 2) : (choose n k).factorization p ≤ 1 :=
begin
  apply factorization_choose_le_log.trans,
  rcases n.eq_zero_or_pos with rfl | hn0, { simp },
  refine lt_succ_iff.1 ((lt_pow_iff_log_lt _ hn0).1 p_large),
  contrapose! hn0,
  exact lt_succ_iff.1 (lt_of_lt_of_le p_large (pow_le_one' hn0 2)),
end

lemma factorization_choose_of_lt_three_mul
  (hp' : p ≠ 2) (hk : p ≤ k) (hk' : p ≤ n - k) (hn : n < 3 * p) :
  (choose n k).factorization p = 0 :=
begin
  cases em' p.prime with hp hp, { exact factorization_eq_zero_of_non_prime _ hp },
  cases lt_or_le n k with hnk hkn, { simp [choose_eq_zero_of_lt hnk] },
  simp only [hp.factorization_choose hkn (lt_add_one _)],
  simp only [finset.card_eq_zero, finset.filter_eq_empty_iff, not_le],
  intros i hi,
  rcases eq_or_lt_of_le (finset.mem_Ico.mp hi).1 with rfl | hi,
  { rw [pow_one, ←add_lt_add_iff_left (2 * p), ←succ_mul, two_mul, add_add_add_comm],
    exact lt_of_le_of_lt (add_le_add
      (add_le_add_right (le_mul_of_one_le_right' ((one_le_div_iff hp.pos).mpr hk)) (k % p))
      (add_le_add_right (le_mul_of_one_le_right' ((one_le_div_iff hp.pos).mpr hk')) ((n - k) % p)))
      (by rwa [div_add_mod, div_add_mod, add_tsub_cancel_of_le hkn]) },
  { replace hn : n < p ^ i,
    { calc n < 3 * p : hn
      ... ≤ p * p : mul_le_mul_right' (lt_of_le_of_ne hp.two_le hp'.symm) p
      ... = p ^ 2 : (sq p).symm
      ... ≤ p ^ i : pow_le_pow hp.one_lt.le hi },
    rwa [mod_eq_of_lt (lt_of_le_of_lt hkn hn), mod_eq_of_lt (lt_of_le_of_lt tsub_le_self hn),
      add_tsub_cancel_of_le hkn] },
end

/--
Primes greater than about `2 * n / 3` and less than `n` do not appear in the factorization of
`central_binom n`.
-/
lemma factorization_central_binom_of_two_mul_self_lt_three_mul
  (n_big : 2 < n) (p_le_n : p ≤ n) (big : 2 * n < 3 * p) :
  (central_binom n).factorization p = 0 :=
begin
  refine factorization_choose_of_lt_three_mul _ p_le_n (p_le_n.trans _) big,
  { rintro rfl, linarith },
  { rw [two_mul, add_tsub_cancel_left] },
end

lemma factorization_factorial_eq_zero_of_lt (h : n < p) :
  (factorial n).factorization p = 0 :=
begin
  induction n with n hn, { simp },
  rw [factorial_succ, factorization_mul n.succ_ne_zero n.factorial_ne_zero, finsupp.coe_add,
      pi.add_apply, hn (lt_of_succ_lt h), add_zero, factorization_eq_zero_of_lt h],
end

lemma factorization_choose_eq_zero_of_lt (h : n < p) :
  (choose n k).factorization p = 0 :=
begin
  by_cases hnk : n < k, { simp [choose_eq_zero_of_lt hnk] },
  rw [choose_eq_factorial_div_factorial (le_of_not_lt hnk),
      factorization_div (factorial_mul_factorial_dvd_factorial (le_of_not_lt hnk)),
      finsupp.coe_tsub, pi.sub_apply, factorization_factorial_eq_zero_of_lt h, zero_tsub],
end

/--
If a prime `p` has positive multiplicity in the `n`th central binomial coefficient,
`p` is no more than `2 * n`
-/
lemma factorization_central_binom_eq_zero_of_two_mul_lt (h : 2 * n < p) :
  (central_binom n).factorization p = 0 :=
factorization_choose_eq_zero_of_lt h

/--
Contrapositive form of `nat.factorization_central_binom_eq_zero_of_two_mul_lt`
-/
lemma le_two_mul_of_factorization_central_binom_pos
  (h_pos : 0 < (central_binom n).factorization p) : p ≤ 2 * n :=
le_of_not_lt (pos_iff_ne_zero.mp h_pos ∘ factorization_central_binom_eq_zero_of_two_mul_lt)

/-- A binomial coefficient is the product of its prime factors, which are at most `n`. -/
lemma prod_pow_factorization_choose (n k : ℕ) (hkn : k ≤ n) :
  ∏ p in (finset.range (n + 1)),
    p ^ ((nat.choose n k).factorization p)
  = choose n k :=
begin
  nth_rewrite_rhs 0 ←factorization_prod_pow_eq_self (choose_pos hkn).ne',
  rw eq_comm,
  apply finset.prod_subset,
  { intros p hp,
    rw finset.mem_range,
    contrapose! hp,
    rw [finsupp.mem_support_iff, not_not, factorization_choose_eq_zero_of_lt hp] },
  { intros p _ h2, simp [not_not.1 (mt finsupp.mem_support_iff.2 h2)] },
end

/-- The `n`th central binomial coefficient is the product of its prime factors, which are
at most `2n`. -/
lemma prod_pow_factorization_central_binom (n : ℕ) :
  ∏ p in (finset.range (2 * n + 1)),
    p ^ ((central_binom n).factorization p)
  = central_binom n :=
begin
  apply prod_pow_factorization_choose,
  linarith,
end

end nat
