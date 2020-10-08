/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson.
-/

import number_theory.arithmetic_function
import number_theory.lucas_lehmer

/-!
# Perfect Numbers

This file proves (currently one direction of)
  Theorem 70 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The theorem characterizes even perfect numbers.

Euclid proved that if `2 ^ (k + 1) - 1` is prime (these primes are known as Mersenne primes),
  then `2 ^ k * 2 ^ (k + 1) - 1` is perfect.

Euler proved the converse, that if `n` is even and perfect, then there exists `k` such that
  `n = 2 ^ k * 2 ^ (k + 1) - 1` and `2 ^ (k + 1) - 1` is prime.

## References
https://en.wikipedia.org/wiki/Euclid%E2%80%93Euler_theorem
-/

@[simp]
lemma succ_mersenne (k : ℕ) : mersenne k + 1 = 2 ^ k :=
begin
  rw [mersenne, ← nat.succ_eq_add_one, ← nat.pred_eq_sub_one, nat.succ_pred_eq_of_pos],
  apply pow_pos,
  dec_trivial,
end

lemma odd_mersenne_succ (k : ℕ) : ¬ 2 ∣ mersenne (k + 1) :=
begin
  rw [← even_iff_two_dvd, ← nat.even_succ, nat.succ_eq_add_one, succ_mersenne,
    even_iff_two_dvd, pow_succ],
  apply dvd.intro _ rfl,
end

namespace nat
open arithmetic_function finset
open_locale arithmetic_function

lemma sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) :=
begin
  simp only [mersenne, prime_two, divisors_prime_pow, sum_map, function.embedding.coe_fn_mk,
    pow_one, sigma_apply],
  induction k,
  { simp },
  rw [pow_succ, sum_range_succ, two_mul, k_ih, nat.add_sub_assoc],
  rw nat.succ_le_iff,
  apply pow_pos,
  dec_trivial,
end

/-- Euclid's theorem that Mersenne primes induce perfect numbers -/
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).prime) :
  perfect ((2 ^ k) * mersenne (k + 1)) :=
begin
  rw [perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ, ← sigma_one_apply, mul_comm,
    is_multiplicative_sigma.map_mul_of_coprime
        (nat.prime_two.coprime_pow_of_not_dvd (odd_mersenne_succ _)),
    sigma_two_pow_eq_mersenne_succ],
  simp [pr, nat.prime_two]
end

end nat
