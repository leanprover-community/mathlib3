/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Bolton Bailey
-/
import data.nat.choose.factorization
import number_theory.primorial
import analysis.convex.specific_functions

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

namespace bertrand

section real

open real

private lemma log_four_pos : 0 < log 4 := log_pos (by linarith)

-- This is best possible; it is false for x = 99.
lemma inequality1 {x : ℝ} (n_large : 100 ≤ x) : log x / (x * log 4) ≤ 1/30 :=
calc log x / (x * log 4) = (log x / x) / log 4 : by field_simp
  ... ≤ log 100 / 100 / log 4 :
          begin
            rw div_le_div_right log_four_pos,
            apply log_div_self_antitone_on,
            { rw set.mem_set_of,
              linarith only [exp_one_lt_d9], },
            { rw set.mem_set_of,
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
          end

-- This is best possible: it is false for x = 312.
lemma inequality2 {x : ℝ} (n_large : 313 ≤ x) : sqrt 2 * sqrt x * log 2 / (x * log 4) ≤ 0.04 :=
begin
  have x_pos : 0 < x := by linarith,
  have four_eq_two_rpow_two : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num,
  rw [div_le_iff (mul_pos x_pos log_four_pos), ←mul_assoc, four_eq_two_rpow_two, log_rpow two_pos,
      ←mul_assoc, mul_le_mul_right (log_pos one_lt_two), ←le_div_iff (sqrt_pos.mpr x_pos),
      mul_comm _ x, mul_assoc, mul_comm x, mul_div_assoc, div_sqrt, mul_comm],
  rw [←div_le_iff],
  { rw [le_sqrt _ (le_of_lt x_pos), div_pow, sq_sqrt (le_of_lt two_pos)],
    { ring_nf, linarith, },
    { rw div_nonneg_iff, simp only [sqrt_nonneg 2, one_div], norm_num, }, },
  { norm_num, },
end

lemma inequality3' {x : ℝ} (x_pos : 0 < x) :
  sqrt 2 * sqrt x * log x / (x * log 4) = (sqrt 2 / log 4) * log x / sqrt x :=
begin
  have: x ≠ 0 := by linarith,
  have: log 4 * sqrt x ≠ 0 := mul_ne_zero log_four_pos.ne' (sqrt_ne_zero'.mpr x_pos),
  field_simp,
  ring_nf,
  rw @sq_sqrt x (by linarith),
  field_simp [log_four_pos.ne'],
  ring_nf,
end

-- This is best possible: it's false for x = 721.
lemma inequality3 {x : ℝ} (n_large : 722 ≤ x) : sqrt 2 * sqrt x * log x / (x * log 4) ≤ 1/4 :=
begin
  have x_pos : 0 < x := by linarith,
  have exp_two_le_722 : exp 2 ≤ 722 :=
  calc
  exp 2 = (exp 1) ^ 2 : by rw [←exp_nat_mul 1 2]; simp
  ... ≤ 3 ^ 2 :
      pow_le_pow_of_le_left (exp_pos 1).le (le_of_lt exp_one_lt_three) 2
  ... ≤ 722 : by norm_num,
  rw [inequality3' x_pos],
  calc sqrt 2 / log 4 * log x / sqrt x
      = sqrt 2 / log 4 * (log x / sqrt x) : by rw mul_div_assoc
  ... ≤ sqrt 2 / log 4 * (log 722 / sqrt 722) :
          begin
            rw mul_le_mul_left (div_pos (sqrt_pos.2 two_pos) log_four_pos),
            exact log_div_sqrt_antitone_on exp_two_le_722 (le_trans exp_two_le_722 n_large) n_large,
          end
  ... = log 722 / log 4 * sqrt 2 / sqrt 722 : by ring
  ... ≤ 1 / 4 :
          begin
            rw [mul_div_assoc, ←sqrt_div zero_le_two],
            norm_num,
            nth_rewrite 1 [(show (361 : ℝ) = (19:ℝ)^2, by norm_num)],
            rw [sqrt_sq],
            field_simp,
            rw div_le_div_iff _ _,
            { rw [one_mul, mul_comm, ←@log_rpow 722 _ 4, mul_comm, ←le_rpow_iff_log_le]; norm_num},
            { refine mul_pos (log_pos _) _; norm_num },
            { norm_num },
            linarith,
          end

end

lemma equality4 (x : ℝ) (n_large : x ≠ 0) : 2 * x / 3 * log 4 / (x * log 4) = 2 / 3 :=
begin
  field_simp [log_four_pos.ne'],
  ring,
end

/--
A reified version of the `bertrand.main_inequality` below.
This is not best possible: it actually holds for 464 ≤ x.
-/
lemma real_main_inequality {x : ℝ} (n_large : (722 : ℝ) ≤ x) :
  x * (2 * x) ^ (sqrt (2 * x)) * 4 ^ (2 * x / 3) ≤ 4 ^ x :=
begin
  apply le_of_lt,
  have v : 0 < (2 * x) ^ (sqrt (2 * x)) := rpow_pos_of_pos (by linarith) _,
  apply (log_lt_log_iff _ (rpow_pos_of_pos four_pos x)).1,
  swap,
  { exact mul_pos (mul_pos (by linarith) v) (rpow_pos_of_pos four_pos _), },
  -- Goal structure gets a bit odd here because there are so many little conditions...
  rw [log_mul, log_mul, log_rpow, log_rpow, log_rpow, log_mul],
  -- Discharge most of the side goals
  repeat { linarith, },
  { rw ←div_lt_one,
    simp only [add_div, mul_add, add_mul, add_div, ←add_assoc, zero_le_one, sqrt_mul, zero_le_bit0],
    { rw [equality4 x (by linarith)],
      have x_100 : 100 ≤ x := by linarith,
      have x_313 : 313 ≤ x := by linarith,
      linarith only [inequality1 x_100, inequality2 x_313, inequality3 n_large], },
      exact mul_pos (by linarith) log_four_pos, },
  repeat {apply ne_of_gt},
  { apply mul_pos _ v, linarith, },
  { exact rpow_pos_of_pos four_pos _, },
end

end real

section nat

open nat

/--
The inequality which contradicts Bertrand's postulate, for large enough `n`.
-/
lemma main_inequality {n : ℕ} (n_large : 722 ≤ n) :
  n * (2 * n) ^ (sqrt (2 * n)) * 4 ^ (2 * n / 3) ≤ 4 ^ n :=
begin
  rw ←@cast_le ℝ,
  have n_large_real : 722 ≤ (n : ℝ),
  { rw ←@cast_le ℝ at n_large,
    convert n_large, norm_num, },
  have n_pos : 0 < (n : ℝ),
  { rw ←cast_zero, norm_num, linarith, },
  have fact2 : 0 < 2 * (n : ℝ) := by linarith,
  simp only [cast_bit0, cast_add, cast_one, cast_mul, cast_pow, ←real.rpow_nat_cast],
  calc
  (n : ℝ) * (2 * (n : ℝ)) ^ (sqrt (2 * n) : ℝ) * 4 ^ (((2 * n / 3) : ℕ) : ℝ)
      ≤ (n : ℝ) * (2 * n : ℝ) ^ (real.sqrt (2 * (n : ℝ))) * 4 ^ (((2 * n / 3) : ℕ) : ℝ) :
          begin
            rw [mul_le_mul_right, mul_le_mul_left n_pos],
            { apply real.rpow_le_rpow_of_exponent_le,
              { linarith, },
              { rw [real.le_sqrt (cast_nonneg _) (le_of_lt fact2), ←cast_pow],
                calc _ ≤ ↑(2 * n) : cast_le.mpr (sqrt_le' _)
                  ... = 2 * (n : ℝ) : by norm_num, }, },
            { apply real.rpow_pos_of_pos,
              norm_num, },
          end
  ... ≤ (n : ℝ) * (2 * n : ℝ) ^ (real.sqrt (2 * (n : ℝ))) * 4 ^ (2 * (n : ℝ) / 3) :
          begin
            have one_le_four : 1 ≤ (4 : ℝ) := by norm_num,
            rw mul_le_mul_left,
            { refine real.rpow_le_rpow_of_exponent_le one_le_four _,
              { apply trans cast_div_le,
                { apply le_of_eq,
                  simp only [cast_bit0, cast_bit1, cast_one, cast_mul], },
                { exact is_trans.swap (λ (x y : ℝ), y ≤ x), }, }, },
            { exact mul_pos n_pos (real.rpow_pos_of_pos fact2 _), },
          end
  ... ≤ 4 ^ (n : ℝ) : real_main_inequality n_large_real,
end

/--
A lemma that tells us that, in the case where Bertrand's postulate does not hold, the prime
factorization of the central binomial coefficent only has factors at most `2 * n / 3 + 1`.
-/
lemma central_binom_factorization_small (n : nat) (n_large : 2 < n)
  (no_prime: ¬∃ (p : ℕ), p.prime ∧ n < p ∧ p ≤ 2 * n) :
  ∏ p in (finset.range (2 * n / 3 + 1)),
    p ^ ((central_binom n).factorization p)
  =
  ∏ p in (finset.range (2 * n + 1)),
    p ^ ((central_binom n).factorization p) :=
begin
  apply finset.prod_subset,
  { -- apply finset.filter_subset_filter,
    rw [finset.range_subset, add_le_add_iff_right],
    apply nat.div_le_of_le_mul,
    linarith, },
  intro x,
  rw [finset.mem_range, finset.mem_range],
  intros hx h2x,
  simp only [hx, and_true, not_lt] at h2x,
  by_contradiction,
  have x_le_two_mul_n : x ≤ 2 * n,
  { apply le_two_mul_of_factorization_central_binom_pos,
    contrapose! h,
    rw nat.eq_zero_of_le_zero h,
    exact pow_zero x, },
  apply no_prime,
  -- ⟨x, ⟨hx, ⟨_, x_le_two_mul_n⟩⟩⟩,
  use x,
  cases le_or_gt x n with x_le_n n_lt_x,
  { rw [add_one, succ_le_iff, div_lt_iff_lt_mul' three_pos, mul_comm x] at h2x,
    have x_non_div :=
      factorization_central_binom_of_two_mul_self_lt_three_mul n_large x_le_n h2x,
    rw [x_non_div, pow_zero] at h,
    simp only [eq_self_iff_true, not_true] at h,
    exfalso, exact h, },
  { have : x.prime,
  { contrapose! h,
    simp [h], },
    exact ⟨this, n_lt_x, x_le_two_mul_n⟩, },
end

/--
An upper bound on the central binomial coefficient used in the proof of Bertrand's postulate.
The bound splits the prime factors of `central_binom n` into those
1. At most `sqrt (2 * n)`, which contribute at most `2 * n` for each such prime.
2. Between `sqrt (2 * n)` and `2 * n / 3`, which contribute at most `4^(2 * n / 3)` in total.
3. Between `2 * n / 3` and `n`, which do not exist.
4. Between `n` and `2 * n`, which would not exist in the case where Bertrand's postulate is false.
5. Above `2 * n`, which do not exist.
-/
lemma central_binom_le_of_no_bertrand_prime (n : ℕ) (n_big : 2 < n)
  (no_prime : ¬∃ (p : ℕ), nat.prime p ∧ n < p ∧ p ≤ 2 * n) :
  central_binom n
    ≤ (2 * n) ^ (sqrt (2 * n))
      * 4 ^ (2 * n / 3) :=
calc
central_binom n
    = ∏ p in (finset.range (2 * n + 1)),
        p ^ ((central_binom n).factorization p) : n.central_binom_factorization_prod_pow.symm
... = (∏ p in (finset.range (2 * n / 3 + 1)),
          p ^ ((central_binom n).factorization p)) :
          (central_binom_factorization_small n (by linarith) no_prime).symm
... = (∏ p in (finset.range (2 * n / 3 + 1)),
          if p ≤ sqrt (2 * n)
          then p ^ ((central_binom n).factorization p)
          else p ^ ((central_binom n).factorization p)) : by simp only [if_t_t]
... = (∏ p in ((finset.range (2 * n / 3 + 1))).filter (≤ sqrt (2 * n)),
          p ^ ((central_binom n).factorization p))
        *
      (∏ p in ((finset.range (2 * n / 3 + 1))).filter (λ p, ¬p ≤ sqrt (2 * n)),
          p ^ ((central_binom n).factorization p)) : finset.prod_ite _ _
... = (∏ p in ((finset.range (2 * n / 3 + 1))).filter (≤ sqrt (2 * n)),
          p ^ ((central_binom n).factorization p))
        *
      (∏ p in ((finset.range (2 * n / 3 + 1))).filter (> sqrt (2 * n)),
          p ^ ((central_binom n).factorization p)) :
        by simp only [not_le, finset.filter_congr_decidable]
... = (∏ p in ((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (≤ sqrt (2 * n)),
          p ^ ((central_binom n).factorization p))
        *
      (∏ p in ((finset.range (2 * n / 3 + 1))).filter (> sqrt (2 * n)),
          p ^ ((central_binom n).factorization p)) :
        begin
          congr' 1,
          symmetry,
          refine finset.prod_subset
                  (finset.filter_subset_filter _ (finset.filter_subset nat.prime _)) _,
          simp only [finset.mem_filter, finset.mem_range, finset.mem_Ico],
          intros x hx hx',
          have not_prime_x : ¬ nat.prime x, tauto,
          simp [not_prime_x],
        end
... ≤ (∏ p in ((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (≤ sqrt (2 * n)), 2 * n)
        *
      (∏ p in ((finset.range (2 * n / 3 + 1))).filter (> sqrt (2 * n)),
          p ^ ((central_binom n).factorization p)) :
        begin
          refine (nat.mul_le_mul_right _ _),
          refine (finset.prod_le_prod'' _),
          intros i hyp,
          exact pow_factorization_choose_le (by linarith),
        end
... = (2 * n) ^ (((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (≤ sqrt (2 * n))).card
      *
      (∏ p in ((finset.range (2 * n / 3 + 1))).filter (> sqrt (2 * n)),
          p ^ ((central_binom n).factorization p)) : by simp only [finset.prod_const]
... = (2 * n) ^ (((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (λ p, p ^ 2 < 2 * n)).card
      *
      (∏ p in ((finset.range (2 * n / 3 + 1))).filter (> sqrt (2 * n)),
          p ^ ((central_binom n).factorization p)) :
        begin
          congr' 3,
          ext1,
          simp only [and_imp, finset.mem_filter, finset.mem_range, and.congr_right_iff],
          intros a_small a_prime,
          rw [le_sqrt', le_iff_eq_or_lt, or_iff_right_iff_imp],
          intro a_sq_even,
          exfalso,
          have a_even := even_two_mul n,
          rw [←a_sq_even, even_pow, nat.prime.even_iff a_prime] at a_even,
          rw a_even.left at a_sq_even,
          norm_num at a_sq_even,
          linarith,
        end
... ≤ (2 * n) ^ (sqrt (2 * n))
        *
      (∏ p in ((finset.range (2 * n / 3 + 1))).filter (> sqrt (2 * n)),
          p ^ ((central_binom n).factorization p)) :
        begin
          refine (nat.mul_le_mul_right _ _),
          refine pow_le_pow (by linarith) _,
          have : (finset.Ico 1 (sqrt (2 * n) + 1)).card = sqrt (2 * n) := by simp,
          rw ←this,
          clear this,
          apply finset.card_mono,
          rw [finset.le_eq_subset, finset.subset_iff],
          simp only [and_imp, finset.mem_filter, finset.mem_range, finset.mem_Ico],
          intros x _ x_prime h,
          split,
          { exact le_of_lt (nat.prime.one_lt x_prime), },
          { rw [lt_succ_iff, le_sqrt'],
            exact le_of_lt h, },
        end
... = (2 * n) ^ (sqrt (2 * n))
        *
      (∏ p in ((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (> sqrt (2 * n)),
          p ^ ((central_binom n).factorization p)) :
        begin
          congr' 1,
          symmetry,
          refine finset.prod_subset
                  (finset.filter_subset_filter _ (finset.filter_subset nat.prime _)) _,
          simp only [finset.mem_filter, finset.mem_range, finset.mem_Ico],
          intros x hx hx',
          have not_prime_x : ¬ nat.prime x, tauto,
          simp [not_prime_x],
        end
... ≤ (2 * n) ^ (sqrt (2 * n))
        *
      (∏ p in ((finset.range (2 * n / 3 + 1)).filter nat.prime).filter (> sqrt (2 * n)),
          p ^ 1) :
      begin
        refine nat.mul_le_mul_left _ _,
        { refine finset.prod_le_prod'' _,
          simp only [finset.mem_filter, finset.mem_range],
          rintros i ⟨hi, sqrt_two_n_lt_i⟩,
          refine pow_le_pow _ _,
          { cases le_or_gt 1 i,
            { exact h, },
            { have i_zero : i = 0, by linarith,
              rw i_zero at *,
              exfalso,
              simp at sqrt_two_n_lt_i,
              exact sqrt_two_n_lt_i, }, },
          { refine nat.factorization_choose_le_one _,
            exact (@sqrt_lt' (2 * n) i).1 sqrt_two_n_lt_i, }, },
      end
... ≤ (2 * n) ^ (sqrt (2 * n))
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
              simp only [i_zero, true_and, succ_pos',
                          finset.mem_filter, finset.mem_range] at hyp1,
              exfalso, exact not_prime_zero hyp1, }, }
        end
... = (2 * n) ^ (sqrt (2 * n))
        *
      (∏ p in (finset.range (2 * n / 3 + 1)).filter nat.prime,
          p) : by simp only [pow_one]
... = (2 * n) ^ (sqrt (2 * n))
        *
      (primorial (2 * n / 3)) : by unfold primorial
... ≤ (2 * n) ^ (sqrt (2 * n))
        *
      4 ^ (2 * n / 3) : nat.mul_le_mul_left _ (primorial_le_4_pow (2 * n / 3))

end nat

end bertrand

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
          nat.mul_le_mul_of_nonneg_left
            (bertrand.central_binom_le_of_no_bertrand_prime n (by linarith) no_prime)
    ... = n * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3) : by ring,
  exact not_le_of_lt false_inequality (bertrand.main_inequality n_big),
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
  { simp only [list.nil_append, list.head_cons] at hn,
    interval_cases n,
    { use 2,
      norm_num, }, },
  { simp only [list.mem_cons_iff, forall_eq_or_imp] at prime_plist,
    by_cases plist_hd ≤ 2 * n,
    { use plist_hd,
      exact ⟨prime_plist.left, hn, h⟩, },
    { apply plist_ih prime_plist.right,
      { intros a b hmem,
        apply covering,
        cases plist_tl,
        { simp only [list.nil_append, list.tail_cons, list.zip_nil_right, list.not_mem_nil] at hmem,
          exfalso, exact hmem, },
        { simp only [list.cons_append, list.tail_cons] at hmem,
          right,
          exact hmem, }, },
      { cases plist_tl,
        { have h_hd := covering plist_hd 2,
          simp only [list.singleton_append, list.tail_cons, list.zip_cons_cons, list.zip_nil_right,
            list.mem_singleton, eq_self_iff_true, forall_true_left] at h_hd,
          have hn2 : 2 * n < 2 * 2 := by linarith only [h, h_hd],
          exact lt_of_mul_lt_mul_left' hn2, },
        { simp only [list.cons_append, list.head_cons],
          have h_hd := covering plist_hd plist_tl_hd,
          simp only [list.cons_append, list.tail_cons, list.zip_cons_cons, list.mem_cons_iff,
            eq_self_iff_true, true_or, forall_true_left] at h_hd,
          rw [not_le] at h,
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
  -- If `n` is large, apply the lemma derived from the inequalities on the central binomial
  -- coefficient.
  { exact bertrand_eventually n h, },
  -- For small `n`, supply a list of primes to cover the initial cases.
  apply bertrand_initial n n_pos [727, 631, 317, 163, 83, 43, 23, 13, 7, 5, 3],
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
    iterate { cases hab <|> rw [hab.left, hab.right] <|> linarith, }, },
  { -- The first element of the list is large enough.
    rw [list.cons_append, list.head],
    linarith, },
end
