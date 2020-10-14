/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson.
-/

import number_theory.arithmetic_function
import number_theory.lucas_lehmer
import algebra.geom_sum

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

lemma odd_mersenne_succ (k : ℕ) : ¬ 2 ∣ mersenne (k + 1) :=
by simp [← even_iff_two_dvd, ← nat.even_succ, nat.succ_eq_add_one] with parity_simps

namespace nat
open arithmetic_function finset
open_locale arithmetic_function

lemma sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) :=
by simpa [mersenne, prime_two, ← geom_sum_mul_add 1 (k+1)]


/-- Euclid's theorem that Mersenne primes induce perfect numbers -/
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).prime) :
  perfect ((2 ^ k) * mersenne (k + 1)) :=
begin
  rw [perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ, ← sigma_one_apply, mul_comm,
    is_multiplicative_sigma.map_mul_of_coprime
        (nat.prime_two.coprime_pow_of_not_dvd (odd_mersenne_succ _)),
    sigma_two_pow_eq_mersenne_succ],
  { simp [pr, nat.prime_two] },
  { apply mul_pos (pow_pos _ k) (mersenne_pos (nat.succ_pos k)),
    norm_num }
end

lemma ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).prime) :
  k ≠ 0 :=
begin
  rintro rfl,
  simpa [mersenne, not_prime_one] using pr,
end

theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).prime) :
  even ((2 ^ k) * mersenne (k + 1)) :=
by simp [ne_zero_of_prime_mersenne k pr] with parity_simps

end nat
