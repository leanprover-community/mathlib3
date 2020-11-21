/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/
import algebra.group_power.identities
import data.int.nat_prime
import tactic.linarith
import tactic.norm_cast
import data.set.finite
/-!
# IMO 1969 Q1

Prove that there are infinitely many natural numbers $a$ with the following property:
the number $z = n^4 + a$ is not prime for any natural number $n$.
-/

open int nat

/-- `good_nats` is the set of natural numbers satisfying the condition in the problem
statement, namely the `a : ℕ` such that `n^4 + a` is not prime for any `n : ℕ`. -/
def good_nats : set ℕ := {a : ℕ | ∀ n : ℕ, ¬ prime (n^4 + a)}

/-!
The key to the solution is that you can factor $z$ into the product of two polynomials,
if $a = 4*m^4$. This is Sophie Germain's identity, called `pow_four_add_four_mul_pow_four`
in mathlib.
-/
lemma factorization {m n : ℤ} : ((n - m)^2 + m^2) * ((n + m)^2 + m^2) = n^4 + 4*m^4 :=
pow_four_add_four_mul_pow_four.symm

/-!
To show that the product is not prime, we need to show each of the factors is at least 2,
which `nlinarith` can solve since they are each expressed as a sum of squares.
-/
lemma left_factor_large {m : ℤ} (n : ℤ) (h : 1 < m) : 1 < ((n - m)^2 + m^2) := by nlinarith
lemma right_factor_large {m : ℤ} (n : ℤ) (h : 1 < m) : 1 < ((n + m)^2 + m^2) := by nlinarith

/-!
The factorization is over the integers, but we need the nonprimality over the natural numbers.
-/
lemma int_large {m : ℤ} (h : 1 < m) : 1 < m.nat_abs :=
by exact_mod_cast lt_of_lt_of_le h le_nat_abs

lemma not_prime_of_int_mul' {m n : ℤ} {c : ℕ}
  (hm : 1 < m) (hn : 1 < n) (hc : m*n = (c : ℤ)) : ¬ prime c :=
not_prime_of_int_mul (int_large hm) (int_large hn) hc

/-- Every natural number of the form `n^4 + 4*m^4` is not prime. -/
lemma polynomial_not_prime {m : ℕ} (h1 : 1 < m) (n : ℕ) : ¬ prime (n^4 + 4*m^4) :=
have h2 : 1 < (m : ℤ), from coe_nat_lt.mpr h1,
begin
  refine not_prime_of_int_mul' (left_factor_large (n : ℤ) h2) (right_factor_large (n : ℤ) h2) _,
  exact_mod_cast factorization
end

/--
We define $a_{choice}(b) := 4*(2+b)^4$, so that we can take $m = 2+b$ in `polynomial_not_prime`.
-/
def a_choice (b : ℕ) : ℕ := 4*(2+b)^4

lemma a_choice_good (b : ℕ) : a_choice b ∈ good_nats :=
polynomial_not_prime (show 1 < 2+b, by linarith)

/-- `a_choice` is a strictly monotone function; this is easily proven by chaining together lemmas
in the `strict_mono` namespace. -/
lemma a_choice_strict_mono : strict_mono a_choice :=
((strict_mono_id.const_add 2).nat_pow (dec_trivial : 0 < 4)).const_mul (dec_trivial : 0 < 4)

/-- We conclude by using the fact that `a_choice` is an injective function from the natural numbers
to the set `good_nats`. -/
theorem imo1969_q1 : set.infinite {a : ℕ | ∀ n : ℕ, ¬ prime (n^4 + a)} :=
set.infinite_of_injective_forall_mem a_choice_strict_mono.injective a_choice_good
