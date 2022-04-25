/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Bolton Bailey
-/
import data.nat.multiplicity
import data.nat.choose.central
import number_theory.padics.padic_norm
import data.complex.exponential_bounds
import number_theory.primorial
import analysis.special_functions.pow

/-!
# Bertrand's Postulate

This file contains a proof of Bertrand's postulate: That between any positive number and its
double there is a prime.

The proof follows the outline of the Erdős proof presented in "Proofs from THE BOOK": One considers
the prime factorization of `(2 * n).choose n`, and splits the constituent primes up into various
groups, then upper bounds the contribution of each group. This upper bounds the central binomial
coefficient, and if the postulate does not hold, this upper bound conflicts with a simple lower
bound for large enough `n`. This proves the result holds for large enough `n`, and for smaller `n`
an explicit list of primes is provided which covers the remaining cases.

As in the [Metamath implementation](carneiro2015arithmetic), we rely on some optimizations from
[Shigenori Tochiori](tochiori_bertrand). In particular we use the fact that `(log x) / x` is
decreasing for `e ≤ x`.

## Proof Sketch

Here is a description of how the proof works:

Then:
4^n ≤ 2nCn * (2 * n + 1) (by choose_halfway_is_big)
= prod (primes ≤ 2n) p^(α n p) * (2n+1)
= prod (primes ≤ n) p^(α n p) * prod (primes n < p <= 2n) p^α * (2n+1)
= prod (primes ≤ 2n/3) p^α * prod (primes 2n/3 to n) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
= prod (primes ≤ 2n/3) p^α * prod (primes 2n/3 to n) 1 * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by claim 3)
= prod (primes ≤ 2n/3) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
= prod (primes ≤ sqrt(2n)) p^α * prod(primes sqrt(2n)..2n/3) p^α
  * prod (primes n < p ≤ 2n) p^α * (2n+1)
≤ prod (primes ≤ sqrt(2n)) p^α * prod(primes sqrt(2n)..2n/3) p
  * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by claim 2)
≤ prod (primes ≤ sqrt(2n)) p^α * 4 ^ (2n / 3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by a general bound on the primorial)
≤ prod (primes ≤ sqrt(2n)) (2n) * 4 ^ (2n / 3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by claim 1)
= (2n)^π (sqrt 2n) * 4 ^ (2n/3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
≤ (2n)^(sqrt 2n) * 4 ^ (2n/3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by "prime count of x is less than x")

For sufficiently large n, that last product term is > 1.
Indeed, suppose for contradiction it's equal to 1.
Then 4^n ≤ (2n)^(sqrt 2n) * 4^(2n/3) * (2n+1)
so 4^(n/3) ≤ (2n)^(sqrt 2n) (2n+1)
and this is Clearly False for sufficiently large n.

## References

* [M. Aigner and G. M. Ziegler _Proofs from THE BOOK_][aigner1999proofs]
* [S. Tochiori, _Considering the Proof of “There is a Prime between n and 2n”_][tochiori_bertrand]
* [M. Carneiro, _Arithmetic in Metamath, Case Study: Bertrand's Postulate_][carneiro2015arithmetic]
-/

open_locale big_operators

section nat

open nat

/-- The multiplicity of p in the nth central binomial coefficient-/
private def α (n p : nat) [hp : fact p.prime] : nat :=
padic_val_nat p (central_binom n)

lemma pow_α_le_two_mul (p : nat) [hp : fact p.prime] (n : nat) (n_big : 3 ≤ n) :
  p ^ (α n p) ≤ 2 * n :=
begin
  unfold α,
  rw @padic_val_nat_def p hp (central_binom n) (nat.pos_of_ne_zero (central_binom_ne_zero n)),
  simp only [central_binom_eq_two_mul_choose n,
    prime.multiplicity_choose hp.out
      (le_mul_of_pos_left zero_lt_two) (lt_add_one (p.log (2 * n)))],
  have r : 2 * n - n = n,
  { calc 2 * n - n = n + n - n : congr_arg (flip (has_sub.sub) n) (two_mul n)
      ... = n : nat.add_sub_cancel n n, },
  simp [r, ←two_mul],
  apply trans (pow_le_pow (trans one_le_two hp.out.two_le) _) (_ : p ^ p.log (2 * n) ≤ 2 * n),
  { calc _ ≤ (finset.Ico 1 (log p (2 * n) + 1)).card : finset.card_filter_le _ _
      ... = (p.log (2 * n) + 1) - 1                  : card_Ico _ _ },
  { apply pow_log_le_self,
    exact hp.out.one_lt,
    linarith, }
end

lemma multiplicity_implies_small (p : nat) [hp : fact p.prime] (n : nat)
  (multiplicity_pos : 0 < α n p) : p ≤ 2 * n :=
begin
  unfold α at multiplicity_pos,
  rw central_binom_eq_two_mul_choose at multiplicity_pos,
  rw @padic_val_nat_def p hp ((2 * n).choose n) (nat.pos_of_ne_zero (central_binom_ne_zero n)) at
    multiplicity_pos,
  simp only [prime.multiplicity_choose hp.out (le_mul_of_pos_left zero_lt_two)
              (lt_add_one (p.log (2 * n)))]
    at multiplicity_pos,
  have r : 2 * n - n = n,
  { calc 2 * n - n = n + n - n : congr_arg (flip (has_sub.sub) n) (two_mul n)
      ... = n : nat.add_sub_cancel n n, },
  simp only [r, ←two_mul, gt_iff_lt, enat.get_coe', finset.filter_congr_decidable]
    at multiplicity_pos,
  rw finset.card_pos at multiplicity_pos,
  cases multiplicity_pos with m hm,
  simp only [finset.mem_Ico, finset.mem_filter] at hm,
  calc p = p ^ 1 : (pow_one _).symm
    ... ≤ p ^ m : pow_le_pow_of_le_right (trans zero_lt_one hp.out.one_lt) hm.left.left
    ... ≤ 2 * (n % p ^ m) : hm.right
    ... ≤ 2 * n : nat.mul_le_mul_left _ (mod_le n _),
end

lemma two_n_div_3_le_central_binom (n : ℕ) : 2 * n / 3 < central_binom n :=
begin
  cases n,
  { simp only [succ_pos', choose_self, nat.zero_div, mul_zero, central_binom_zero], },
  calc 2 * (n + 1) / 3 < 2 * (n + 1)            : nat.div_lt_self (by norm_num) (by norm_num)
    ... = (2 * (n + 1)).choose(1)               : by norm_num
    ... ≤ (2 * (n + 1)).choose(2 * (n + 1) / 2) : choose_le_middle 1 (2 * (n + 1))
    ... = (2 * (n + 1)).choose(n + 1)           : by simp only [succ_pos', mul_div_right],
end

lemma central_binom_factorization (n : ℕ) :
  ∏ p in finset.filter nat.prime (finset.range (central_binom n + 1)),
    p ^ (padic_val_nat p (central_binom n))
  = central_binom n :=
  prod_pow_prime_padic_val_nat _ (central_binom_ne_zero n) _ (lt_add_one _)

lemma intervening_sqrt {a n : ℕ} (small : (sqrt n) ^ 2 ≤ a ^ 2) (big : a ^ 2 ≤ n)
  : a = sqrt n :=
begin
  rcases lt_trichotomy a (sqrt n) with H|rfl|H,
  { refine (lt_irrefl (a ^ 2) _).elim,
    calc a ^ 2 = a * a      : sq _
      ... < n.sqrt * n.sqrt : mul_self_lt_mul_self H
      ... = (sqrt n) ^ 2    : (sq _).symm
      ... ≤ a ^ 2           : small, },
  { refl, },
  { refine (lt_irrefl (a ^ 2) _).elim,
    calc a ^ 2 ≤ n : big
      ... < a * a : sqrt_lt.1 H
      ... = a ^ 2 : (sq _).symm, },
end

lemma even_prime_is_two {p : ℕ} (pr: p.prime) (div: 2 ∣ p) : p = 2 :=
((prime_dvd_prime_iff_eq prime_two pr).mp div).symm

lemma sq_prime_is_small {p n : ℕ} (hp : nat.prime p) (n_big : 2 < n) (small : p ≤ sqrt (2 * n)) :
  p ^ 2 < 2 * n :=
begin
  cases lt_or_ge (p ^ 2) (2 * n),
  { exact h, },
  { have small' : p ^ 2 ≤ (2 * n) := le_sqrt'.mp small,
    have t : p * p = 2 * n := (sq _).symm.trans (small'.antisymm h),
    have p_even : 2 ∣ p := (or_self _).mp ((prime.dvd_mul prime_two).mp ⟨n, t⟩),
    have p_two : p = 2 := even_prime_is_two hp p_even,
    rw [p_two, sq],
    exact (mul_lt_mul_left zero_lt_two).mpr n_big },
end

end nat

section real_inequalities
open real

lemma one_lt_four : (1 : ℝ) < 4 := by linarith

lemma log_four_pos : 0 < log 4 := log_pos one_lt_four

lemma log_four_nonzero : log 4 ≠ 0 := by linarith [log_four_pos]

lemma log_1024_div_log_4 : log 1024 / log 4 = 5 :=
begin
  have h : (1024 : ℝ) = 4 ^ (5 : ℝ) := by norm_num,
  rw [div_eq_iff log_four_nonzero, h, log_rpow],
  linarith,
end

lemma four_eq_two_rpow_two : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num

-- lemma real.mul_div_mul (a b c : ℝ) (ha : a ≠ 0) : (a * b) / (a * c) = b / c :=
-- begin
--   exact mul_div_mul_left b c ha,
--   by_cases c = 0,
--   { subst h, simp, },
--   { field_simp,
--     ring, }
-- end

-- This is best possible; it is false for x = 99.
lemma inequality1 {x : ℝ} (n_large : 100 ≤ x) : log x / (x * log 4) ≤ 1/30 :=
begin
  have h4 : 0 < x := by linarith only [n_large],
  have x_ne_zero := ne_of_gt h4,
  calc log x / (x * log 4) = (log x / x) / log 4 : by field_simp
    ... ≤ log 100 / 100 / log 4 :
            begin
              rw div_le_div_right log_four_pos,
              apply log_div_self_antitone_on,
              { simp only [set.mem_set_of_eq],
                linarith only [exp_one_lt_d9], },
              { simp only [set.mem_set_of_eq],
                linarith only [exp_one_lt_d9, n_large], },
              { exact n_large, },
            end
    ... = log 100 / log 4 / 100 : by ring_nf
    ... = log (10 ^ (2 : ℝ)) / log (2 ^ (2 : ℝ)) / 100 : by norm_num
    ... = (2 * log 10) / log (2 ^ (2 : ℝ)) / 100 : by rw @log_rpow 10 (by norm_num) 2
    ... = ((2 * log 10) / (2 * log 2)) / 100 : by rw @log_rpow 2 (by norm_num) 2
    ... = (log 10 / log 2) / 100 : by { rw mul_div_mul_left (log 10) (log 2), norm_num, }
    ... ≤ 1 / 30 :
            begin
              have thousand_pos : 0 < (1000 : ℝ) := by norm_num,
              cancel_denoms,
              rw mul_div,
              have log_2_pos : 0 < log 2 := log_pos (by norm_num),
              rw div_le_iff log_2_pos,
              calc 3 * log 10 = log (10 ^ 3) : eq.symm (log_rpow (by norm_num) 3)
                ... = log 1000 : by norm_num
                ... ≤ log 1024 : (log_le_log thousand_pos (by norm_num)).2 (by norm_num)
                ... = log (2 ^ (10 : ℝ)) : by norm_num
                ... = 10 * log 2 : log_rpow (by norm_num) 10
            end,
end

-- This is best possible: it is false for x = 312.
lemma inequality2 {x : ℝ} (n_large : 313 ≤ x) : sqrt 2 * sqrt x * log 2 / (x * log 4) ≤ 0.04 :=
begin
  have x_pos : 0 < x := by linarith,
  rw div_le_iff (mul_pos x_pos (log_pos one_lt_four)),
  rw [←mul_assoc, four_eq_two_rpow_two, log_rpow two_pos, ←mul_assoc,
    mul_le_mul_right (log_pos one_lt_two)],
  rw [←le_div_iff (sqrt_pos.mpr x_pos), mul_comm _ x, mul_assoc, mul_comm x, mul_div_assoc],
  rw div_sqrt,
  rw [mul_comm, ←div_le_iff],
  { rw [le_sqrt _ (le_of_lt x_pos), div_pow, sq_sqrt (le_of_lt two_pos)],
    { ring_nf, linarith, },
    { rw div_nonneg_iff, simp only [sqrt_nonneg 2, one_div], norm_num, }, },
  { norm_num, },
end

lemma inequality3' {x : ℝ} (x_pos : 0 < x) :
  sqrt 2 * sqrt x * log x / (x * log 4) = (sqrt 2 / log 4) * log x / sqrt x :=
begin
  have: x ≠ 0 := by linarith,
  have: log 4 * sqrt x ≠ 0 := mul_ne_zero log_four_nonzero (sqrt_ne_zero'.mpr x_pos),
  field_simp,
  ring_nf,
  rw @sq_sqrt x (by linarith),
  field_simp [log_four_nonzero],
  ring_nf,
end

lemma log_div_sqrt_decreasing {x y : ℝ} (hex : exp 2 ≤ x) (hxy : x ≤ y) :
  log y / sqrt y ≤ log x / sqrt x :=
begin
  have x_pos : 0 < x := lt_of_lt_of_le (exp_pos 2) hex,
  have y_pos : 0 < y := by linarith,
  have x_nonneg : 0 ≤ x := le_trans (le_of_lt (exp_pos 2)) hex,
  have y_nonneg : 0 ≤ y := by linarith,
  conv_lhs { congr, rw ←sq_sqrt y_nonneg, },
  conv_rhs { congr, rw ←sq_sqrt x_nonneg, },
  rw [←rpow_nat_cast, ←rpow_nat_cast, log_rpow (sqrt_pos.mpr y_pos), log_rpow (sqrt_pos.mpr x_pos)],
  simp only [nat.cast_bit0, nat.cast_one],
  repeat { rw mul_div_assoc, },
  rw mul_le_mul_left two_pos,
  { refine log_div_self_antitone_on _ _ (sqrt_le_sqrt hxy),
    repeat { simp only [set.mem_set_of_eq],
      rw [le_sqrt (le_of_lt (exp_pos 1)), ←exp_nat_mul],
      norm_num, linarith, linarith, }, },
  { exact real.nontrivial, },
end

lemma real.div_mul_eq_div_div {a b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0) : a / (b * c) = (a / b) / c :=
by field_simp

lemma log_four : log 4 = 2 * log 2 :=
calc log 4 = log (2 ^ (2 : ℝ)) : by norm_num
  ... = 2 * log 2 : by rw log_rpow two_pos

lemma sqrt_361 : sqrt 361 = 19 :=
calc sqrt 361 = sqrt (19 ^ 2) : by norm_num
  ... = 19 : sqrt_sq (by norm_num)

-- open tactic.interactive
-- meta def collapse_log : tactic unit :=
-- do
--   tactic.repeat { tactic.interactive.rw [``(real.log_rpow), ``(real.log_mul)], }
  --tactic.repeat tactic.norm_num,

lemma log_722 : log 722 = log 2 + 2 * log 19 :=
begin
  repeat {
    rw ←log_rpow,
    rw ←log_mul,
  },
  repeat {
    norm_num,
  },
end
--calc log 722 = log (2 * 19 ^ (2 : ℝ)) : by norm_num
--  ... = log 2 + log (19 ^ (2 : ℝ)) : log_mul (by norm_num) (by norm_num)
--  ... = log 2 + 2 * log 19 : by rw @log_rpow 19 (by norm_num)

lemma inequality : log 521284 / log 2 ≤ 19 :=
begin
  rw div_le_iff (log_pos one_lt_two),
  calc log 521284
        ≤ log (2 ^ (19 : ℝ)) : (@log_le_log 521284 _ (by norm_num) (by norm_num)).2 (by norm_num)
    ... = 19 * log 2 : @log_rpow 2 two_pos 19,
end

-- This is best possible: it's false for x = 721.
lemma inequality3 {x : ℝ} (n_large : 722 ≤ x) : sqrt 2 * sqrt x * log x / (x * log 4) ≤ 1/4 :=
begin
  have x_pos : 0 < x := by linarith,
  rw [inequality3' x_pos],
  have bound : log x / sqrt x ≤ log 722 / sqrt 722,
  { refine log_div_sqrt_decreasing _ n_large,
    calc exp 2 = (exp 1) ^ 2 : by rw [←exp_nat_mul 1 2]; simp
      ... ≤ 2.7182818286 ^ 2 :
          pow_le_pow_of_le_left (le_of_lt (exp_pos 1)) (le_of_lt exp_one_lt_d9) _
      ... = 7.38905609969695977796 : by norm_num
      ... ≤ 722 : by linarith, },
  calc sqrt 2 / log 4 * log x / sqrt x
      = sqrt 2 / log 4 * (log x / sqrt x) : by rw mul_div_assoc
  ... ≤ sqrt 2 / log 4 * (log 722 / sqrt 722) :
          begin
            rw mul_le_mul_left,
            { exact bound, },
            { exact div_pos (sqrt_pos.2 two_pos) log_four_pos, },
          end
  ... = log 722 / log 4 * sqrt 2 / sqrt 722 : by ring
  ... ≤ 1 / 4 :
          begin
            rw [mul_div_assoc, ←sqrt_div zero_le_two],
            norm_num,
            field_simp [sqrt_361],
            cancel_denoms,
            rw real.div_mul_eq_div_div,
            { cancel_denoms,
              rw mul_div,
              rw log_722,
              rw log_four,
              have nineteen_pos : (0 : ℝ) < 19 := by norm_num,
              calc 4 * (log 2 + 2 * log 19) / (2 * log 2)
                    = 2 * (2 * (log 2 + 2 * log 19)) / (2 * log 2) : by ring
                ... = 2 * (log 2 + 2 * log 19) / log 2 : mul_div_mul_left _ _ (by norm_num)
                ... = (2 * log 2 + 4 * log 19) / log 2 : by ring
                ... = (log 4 + 4 * log 19) / log 2 : by rw log_four
                ... = (log 4 + log (19 ^ (4 : ℝ))) / log 2 : by rw log_rpow nineteen_pos 4
                ... = (log 4 + log 130321) / log 2 : by norm_num
                ... = log (4 * 130321) / log 2 : by rw @log_mul 4 130321 (by norm_num) (by norm_num)
                ... = log 521284 / log 2 : by norm_num
                ... ≤ 19 : inequality, },
            { norm_num, },
            { norm_num, },
          end,

end

lemma equality4 {x : ℝ} (n_large : x ≠ 0) : 2 * x / 3 * log 4 / (x * log 4) = 2 / 3 :=
begin
  field_simp [log_four_nonzero],
  ring,
end

/--
A reified version of the `bertrand_inequality` below.
This is not best possible: it actually holds for 464 ≤ x.
-/
lemma real_bertrand_inequality {x : ℝ} (n_large : (722 : ℝ) ≤ x)
  : x * (2 * x) ^ (sqrt (2 * x)) * 4 ^ (2 * x / 3) < 4 ^ x :=
begin
  have four_pow_pos : ∀ (k : ℝ), (0 : ℝ) < 4 ^ k,
  { intros k,
    apply rpow_pos_of_pos four_pos, },
  have v : 0 < (2 * x) ^ (sqrt (2 * x)) := rpow_pos_of_pos (by linarith) _,
  apply (log_lt_log_iff _ (four_pow_pos x)).1,
  swap,
  { exact mul_pos (mul_pos (by linarith) v) (four_pow_pos _), },
  -- Goal structure gets a bit odd here because there are so many little conditions...
  rw [log_mul, log_mul, log_rpow, log_rpow, log_rpow, log_mul],
  -- Discharge most of the side goals
  repeat { linarith, },
  { rw <-div_lt_one,
    simp only [add_div, mul_add, add_mul, add_div, ←add_assoc],
    simp only [zero_le_one, sqrt_mul, zero_le_bit0],
    { rw [@equality4 x (by linarith)],
      have x_100 : 100 ≤ x := by linarith,
      have x_313 : 313 ≤ x := by linarith,
      linarith only [inequality1 x_100, inequality2 x_313, inequality3 n_large], },
      exact mul_pos (by linarith) log_four_pos, },
  repeat {apply ne_of_gt},
  { apply mul_pos _ v, linarith, },
  { exact four_pow_pos _, },
end

end real_inequalities

/--
The inequality which contradicts Bertrand's postulate, for large enough `n`.
-/
lemma bertrand_inequality {n : ℕ} (n_large : 722 ≤ n) :
  n * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3) ≤ 4 ^ n :=
begin
  rw ←@nat.cast_le ℝ,
  have fact1 : 0 < (n : ℝ),
  { rw ←nat.cast_zero, norm_num, linarith, },
  have fact2 : 0 < 2 * (n : ℝ) := by linarith,
  simp only [nat.cast_bit0, nat.cast_add, nat.cast_one, nat.cast_mul, nat.cast_pow],
  simp only [←real.rpow_nat_cast],
  apply le_of_lt,
  calc
  (n : ℝ) * (2 * (n : ℝ)) ^ (nat.sqrt (2 * n) : ℝ) * 4 ^ (((2 * n / 3) : ℕ) : ℝ)
      ≤ (n : ℝ) * (2 * n : ℝ) ^ (real.sqrt (2 * (n : ℝ))) * 4 ^ (((2 * n / 3) : ℕ) : ℝ) :
          begin
            rw [mul_le_mul_right, mul_le_mul_left fact1],
            { apply real.rpow_le_rpow_of_exponent_le,
              { rw ←@nat.cast_le ℝ at n_large,
                have h : 722 ≤ (n : ℝ),
                { convert n_large, simp, },
                linarith, },
              rw [real.le_sqrt (nat.cast_nonneg _) (le_of_lt fact2), ←nat.cast_pow],
              calc _ ≤ ↑(2 * n) : nat.cast_le.mpr (nat.sqrt_le' _)
                 ... = 2 * (n : ℝ) : by norm_num, },
            { apply real.rpow_pos_of_pos,
              norm_num, },
          end
  ... ≤ (n : ℝ) * (2 * n : ℝ) ^ (real.sqrt (2 * (n : ℝ))) * 4 ^ (2 * (n : ℝ) / 3) :
          begin
            have one_le_four : 1 ≤ (4 : ℝ) := by norm_num,
            rw mul_le_mul_left,
            apply real.rpow_le_rpow_of_exponent_le one_le_four,
            { apply trans nat.cast_div_le,
              apply le_of_eq,
              congr,
              { simp only [nat.cast_bit0, nat.cast_one, nat.cast_mul], },
              { simp only [nat.cast_bit1, nat.cast_one], },
              { exact is_trans.swap (λ (x y : ℝ), y ≤ x), }, },
            apply mul_pos fact1,
            apply real.rpow_pos_of_pos fact2,
          end
  ... < 4 ^ (n : ℝ) :
          begin
            apply real_bertrand_inequality,
            rw ←@nat.cast_le ℝ at n_large,
            have: 722 ≤ (n : ℝ), { convert n_large, norm_num, },
            linarith,
          end,
end

/--
A lemma that tells us that, in the case where Bertrand's postulate does not hold, the prime
factorization of the central binomial coefficent only has factors at most `2 * n / 3 + 1`.
-/
lemma central_binom_factorization_small (n : nat) (n_large : 2 < n)
  (no_prime: ¬∃ (p : ℕ), p.prime ∧ n < p ∧ p ≤ 2 * n) :
  ∏ p in (finset.range (2 * n / 3 + 1)).filter nat.prime,
    p ^ (padic_val_nat p (nat.central_binom n))
  =
  ∏ p in (finset.range ((nat.central_binom n + 1))).filter nat.prime,
    p ^ (padic_val_nat p (nat.central_binom n)) :=
begin
  apply finset.prod_subset,
  { apply finset.filter_subset_filter,
    rw finset.range_subset,
    rw [add_le_add_iff_right],
    exact le_of_lt (two_n_div_3_le_central_binom n), },
  intro x,
  rw [finset.mem_filter, finset.mem_filter, finset.mem_range, finset.mem_range],
  intros hx h2x,
  simp only [hx.right, and_true, not_lt] at h2x,
  by_contradiction,
  have x_le_two_mul_n : x ≤ 2 * n,
  { apply (@multiplicity_implies_small x ⟨hx.right⟩ n),
    unfold α,
    by_contradiction h1,
    rw [not_lt, le_zero_iff] at h1,
    rw h1 at h,
    rw pow_zero at h,
    simp only [eq_self_iff_true, not_true] at h,
    exact h, },
  apply no_prime,
  use x,
  split,
  { exact hx.right, },
  { split,
    { by_contradiction neg_n_le_x,
      simp only [not_lt] at neg_n_le_x,
      rw [nat.add_one, nat.succ_le_iff, nat.div_lt_iff_lt_mul', mul_comm x] at h2x,
      have claim := @nat.padic_val_nat_central_binom_of_large_eq_zero _ n hx.right (by linarith)
                      (by linarith) h2x,
      rw [claim, pow_zero] at h,
      simp only [eq_self_iff_true, not_true] at h,
      exact h,
      dec_trivial, },
    exact x_le_two_mul_n, },
end

/--
An upper bound on the central binomial coefficient used in the proof of Bertrand's postulate.
The bound splits the prime factors of `central_binom n` into those
1. At most `sqrt (2 * n)`, which contribute at most `2 * n` for each such prime.
2. Between `sqrt (2 * n)` and `2 * n / 3`, which contribute at most `4^(2 * n / 3)` in total.
3. Between `2 * n / 3` and `n`, which do not exist.
4. Above `n`, which do not exist in the case where Bertrand's postulate is false.
-/
lemma bertrand_central_binom_le (n : ℕ) (n_big : 2 < n)
  (no_prime : ¬∃ (p : ℕ), nat.prime p ∧ n < p ∧ p ≤ 2 * n) :
  nat.central_binom n
    ≤ (2 * n) ^ (nat.sqrt (2 * n))
      * 4 ^ (2 * n / 3) :=
calc
nat.central_binom n
    = (∏ p in (finset.range (2 * n / 3 + 1)).filter nat.prime,
          p ^ (padic_val_nat p (nat.central_binom n))) :
          by rw [(central_binom_factorization_small n (by linarith) no_prime),
                  central_binom_factorization]
... = (∏ p in (finset.range (2 * n / 3 + 1)).filter nat.prime,
          if p ≤ nat.sqrt (2 * n)
          then p ^ (padic_val_nat p (nat.central_binom n))
          else p ^ (padic_val_nat p (nat.central_binom n))) : by simp only [if_t_t]
... = (∏ p in ((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (≤ nat.sqrt (2 * n)),
          p ^ (padic_val_nat p (nat.central_binom n)))
        *
      (∏ p in ((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (λ p, ¬p ≤ nat.sqrt (2 * n)),
          p ^ (padic_val_nat p (nat.central_binom n))) : finset.prod_ite _ _
... = (∏ p in ((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (≤ nat.sqrt (2 * n)),
          p ^ (padic_val_nat p (nat.central_binom n)))
        *
      (∏ p in ((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (> nat.sqrt (2 * n)),
          p ^ (padic_val_nat p (nat.central_binom n))) :
        by simp only [not_le, finset.filter_congr_decidable]
... ≤ (∏ p in ((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (≤ nat.sqrt (2 * n)), 2 * n)
        *
      (∏ p in ((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (> nat.sqrt (2 * n)),
          p ^ (padic_val_nat p (nat.central_binom n))) :
        begin
          refine (nat.mul_le_mul_right _ _),
          refine finset.prod_le_prod'' _,
          intros i hyp,
          simp only [finset.mem_filter, finset.mem_range] at hyp,
          exact @pow_α_le_two_mul i (fact_iff.2 hyp.1.2) n (by linarith),
        end
... = (2 * n) ^ (((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (≤ nat.sqrt (2 * n))).card
      *
      (∏ p in ((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (> nat.sqrt (2 * n)),
          p ^ (padic_val_nat p (nat.central_binom n))) : by simp only [finset.prod_const]
... = (2 * n) ^ (((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (λ p, p ^ 2 < 2 * n)).card
      *
      (∏ p in ((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (> nat.sqrt (2 * n)),
          p ^ (padic_val_nat p (nat.central_binom n))) :
        begin
          congr' 3,
          ext1,
          simp only [and_imp, finset.mem_filter, finset.mem_range, and.congr_right_iff],
          intros h pa,
          split,
          { exact sq_prime_is_small pa (by linarith), },
          { rw nat.le_sqrt', exact le_of_lt, },
        end
... ≤ (2 * n) ^ (nat.sqrt (2 * n))
        *
      (∏ p in ((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (> nat.sqrt (2 * n)),
          p ^ (padic_val_nat p (nat.central_binom n))) :
        begin
          refine (nat.mul_le_mul_right _ _),
          refine pow_le_pow (by linarith) _,
          have : (finset.Ico 1 (nat.sqrt (2 * n) + 1)).card = nat.sqrt (2 * n),
          { simp, },
          rw <-this,
          clear this,
          apply finset.card_mono,
          rw [finset.le_eq_subset, finset.subset_iff],
          simp only [and_imp, finset.mem_filter, finset.mem_range, finset.mem_Ico],
          intros x _ px h,
          split,
          { exact le_of_lt (nat.prime.one_lt px), },
          { rw nat.lt_succ_iff,
            rw nat.le_sqrt',
            exact le_of_lt h, },
        end
... ≤ (2 * n) ^ (nat.sqrt (2 * n))
        *
      (∏ p in ((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (> nat.sqrt (2 * n)),
          p ^ 1) :
      begin
        refine nat.mul_le_mul_left _ _,
        { refine finset.prod_le_prod'' _,
          intros i hyp,
          simp only [finset.mem_filter, finset.mem_range] at hyp,
          cases hyp with i_facts sqrt_two_n_lt_i,
          refine pow_le_pow _ _,
          { cases le_or_gt 1 i,
            { exact h, },
            { have i_zero : i = 0, by linarith,
              rw i_zero at i_facts,
              exfalso,
              exact nat.not_prime_zero i_facts.2, }, },
          { apply @nat.padic_val_nat_central_binom_of_large_le_one i n i_facts.2,
            exact (@nat.sqrt_lt' (2 * n) i).1 sqrt_two_n_lt_i, }, },
      end
... ≤ (2 * n) ^ (nat.sqrt (2 * n))
        *
      (∏ p in (finset.range (2 * n / 3 + 1)).filter nat.prime,
          p ^ 1) :
        begin
          refine nat.mul_le_mul_left _ _,
          refine finset.prod_le_prod_of_subset_of_one_le' (finset.filter_subset _ _) _,
          { intros i hyp1 hyp2,
          cases le_or_gt 1 i,
          { ring_nf, exact h, },
          { have i_zero : i = 0, by linarith,
            simp only [i_zero, true_and, nat.succ_pos',
                        finset.mem_filter, finset.mem_range] at hyp1,
            exfalso, exact nat.not_prime_zero hyp1, }, }
        end
... = (2 * n) ^ (nat.sqrt (2 * n))
        *
      (∏ p in (finset.range (2 * n / 3 + 1)).filter nat.prime,
          p) : by simp only [pow_one]
... = (2 * n) ^ (nat.sqrt (2 * n))
        *
      (primorial (2 * n / 3)) : by unfold primorial
... ≤ (2 * n) ^ (nat.sqrt (2 * n))
        *
      4 ^ (2 * n / 3) : nat.mul_le_mul_left _ (primorial_le_4_pow (2 * n / 3))

/--
Proves that Bertrand's postulate holds for all sufficiently large `n`.
-/
lemma bertrand_eventually (n : nat) (n_big : 722 ≤ n) : ∃ (p : ℕ), p.prime ∧ n < p ∧ p ≤ 2 * n :=
begin
  -- Assume there is no prime in the range
  by_contradiction no_prime,
  -- If not, then we have the above upper bound on the size of this central binomial coefficient.
  -- We now couple this bound with a lower bound on the central binomial coefficient, yielding an
  -- inequality which we have seen is false for large enough n.
  have false_inequality : 4 ^ n < n * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3),
  calc 4 ^ n < n * nat.central_binom n : nat.four_pow_lt_mul_central_binom n (by linarith)
    ... ≤ n * ((2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3)) :
          nat.mul_le_mul_of_nonneg_left (bertrand_central_binom_le n (by linarith) no_prime)
    ... = n * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3) : by ring,
  exact not_le_of_lt false_inequality (bertrand_inequality n_big),
end

/--
Proves that Bertrand's postulate holds over all positive naturals less than n by identifying a
descending list of primes, each no more than twice the next, such that the list contains a witness
for each number ≤ n.
-/
lemma bertrand_initial (n : ℕ) (hn0 : 0 < n)
  (plist : list ℕ) (prime_plist : ∀ p ∈ plist, nat.prime p)
  (covering : ∀ a b, (a, b) ∈ list.zip plist (list.tail (plist ++ [2])) → a ≤ 2 * b)
  (hn : n < (plist ++ [2]).head) :
  ∃ (p : ℕ), p.prime ∧ n < p ∧ p ≤ 2 * n :=
begin
  unfreezingI { induction plist, },
  { simp * at *,
    interval_cases n,
    { use 2,
      norm_num, }, },
  { simp * at *,
    by_cases plist_hd ≤ 2 * n,
    { use plist_hd,
      exact ⟨prime_plist.left, hn, h⟩, },
    { apply plist_ih,
      { exact prime_plist.right, },
      { intros a b hmem,
        apply covering,
        cases plist_tl,
        { simp * at *, },
        { simp at hmem,
          simp only [list.mem_cons_iff, list.cons_append, prod.mk.inj_iff, list.zip_cons_cons],
          right,
          assumption, }, },
      { cases plist_tl,
        { simp * at *,
          have h_hd := covering plist_hd 2 rfl rfl,
          have hn2 : 2 * n < 2 * 2, exact gt_of_ge_of_gt h_hd h,
          exact lt_of_mul_lt_mul_left' hn2, },
        { simp * at *,
          have h_hd := covering plist_hd plist_tl_hd,
          simp at h_hd,
          have hn2 : 2 * n < 2 * plist_tl_hd, exact gt_of_ge_of_gt h_hd h,
          exact lt_of_mul_lt_mul_left' hn2, }, }, }, },
end


/--
Bertrand's Postulate: For any positive natural number, there is a prime which is greater than
it, but no more than twice as large.
-/
theorem bertrand (n : nat) (n_pos : 0 < n) : ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
begin
  -- Split into cases whether `n` is large or small
  cases lt_or_le 721 n,
  -- If `n` is large, apply the theorem derived from the inequalities on the central binomial
  -- coefficient.
  { exact bertrand_eventually n h },
  -- For small `n`, supply a list of primes to cover the initial cases.
  apply bertrand_initial n n_pos [1031, 631, 317, 163, 83, 43, 23, 13, 7, 5, 3],
  -- Prove the list has the properties needed:
  { -- The list consists of primes
    intros p hp,
    simp only [list.mem_cons_iff, list.mem_singleton] at hp,
    iterate {cases hp <|> rw hp <|> norm_num}, },
  { -- Each element of the list is at least half the previous.
    intros a b hab,
    simp only [list.zip_nil_right, list.mem_cons_iff, list.cons_append, prod.mk.inj_iff,
               list.zip_cons_cons, list.tail, list.mem_singleton, list.singleton_append,
               list.tail_cons] at hab,
    iterate {cases hab <|> rw [hab.left, hab.right] <|> linarith}, },
  { -- The first element of the list is large enough.
    simp only [list.head, list.cons_append],
    linarith, },
end
