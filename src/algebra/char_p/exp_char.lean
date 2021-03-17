/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jakob Scholbach.
-/
import algebra.char_p.basic
import algebra.char_zero
import data.nat.prime

/-!
# Exponential characteristic

This file defines the exponential characteristic of an integral domain, 
and establishes a few basic facts relating the exponential characteristic to the (ordinary)
characteristic.

## Main results
- `exp_char`: the definition of exponential characteristic
- `exp_char_is_prime_or_one`: the exponential characteristic is a prime or one
- `char_eq_exp_char_iff`: the characteristic equals the exponential characteristic iff the 
  characteristic is prime

## Tags
exponential characteristic, characteristic
-/

universe u
variables (R : Type u) [integral_domain R]

/-- The definition of the exponential characteristic of a semiring. -/
class exp_char (R : Type u) [semiring R] (q : ℕ) : Prop :=
(exp_char_def : (q = 1 ∧ char_zero R) ∨ (q.prime ∧ char_p R q))

/-- The exponential characteristic is one if the characteristic is zero. -/
lemma exp_char_one_of_char_zero (q : ℕ) [hp : char_p R 0] [hq : exp_char R q] :
q = 1 :=
begin
  cases hq.exp_char_def with q_one q_prime,
  { exact q_one.1, },
  { have p_eq_q : 0 = q, { apply char_p.eq R, exact hp, exact q_prime.2,},
    have q_prime : q.prime, { exact  q_prime.1, },
    have : nat.prime 0, { rw p_eq_q, exact q_prime, },
    have : 0 > 0 := this.pos,
    linarith, }
end

/-- The exponential characteristic is one if the characteristic is zero. -/
lemma char_zero_of_exp_char_one (p : ℕ) [hp : char_p R p] [hq : exp_char R 1] :
p = 0 :=
begin
  cases hq.exp_char_def with q_one q_prime,
  { haveI := q_one.2,
    have char0' : char_p R 0, { apply_instance, },
    have p0 : p = 0 := begin apply char_p.eq R hp char0', end,
    tauto, },
  { haveI := q_prime.2,
    have : 1 ≠ 1 := char_p.char_ne_one R 1,
    tauto, }
end

/-- The exponential characteristic is one if the characteristic is zero. -/
lemma char_zero_of_exp_char_one' [hq : exp_char R 1] : char_zero R :=
begin
  cases hq.exp_char_def,
  { exact h.2, },
  { haveI := h.2, 
    have : 1 ≠ 1 := char_p.char_ne_one R 1, 
    tauto, }
end

/-- The exponential characteristic is one iff the characteristic is zero. -/
theorem exp_char_one_iff_char_zero (p q : ℕ) [char_p R p] [exp_char R q] :
q = 1 ↔ p = 0 :=
begin
  split,
  { intro q_1,
    haveI : exp_char R 1 := by { rw ←q_1, assumption, },
    exact char_zero_of_exp_char_one R p, },
  { intro p_0,
    haveI : char_p R 0 := by { rw ←p_0, assumption, },
    exact exp_char_one_of_char_zero R q, }
end

/-- The characteristic of a domain equals the exponential characteristic iff the former is prime. -/
theorem char_eq_exp_char_iff (p q : ℕ) [hp : char_p R p] [hq : exp_char R q] :
p = q ↔ p.prime :=
begin
  cases hq.exp_char_def with q_one q_prime,
  { split,
    { intro hpq, rw q_one.1 at hpq, rw hpq at hp, 
      haveI := q_one.2,
      have : 0 = 1 := char_p.eq R (char_p.of_char_zero R) hp,
      tauto, },
    { intro pprime,
      haveI := q_one.2,
      have char0' : char_p R 0, { apply_instance, },
      have : p = 0 := char_p.eq R hp char0',
      have : p > 0 := pprime.pos, 
      linarith, } },
  { split,
    { intro hpq, rw hpq, exact q_prime.1, },
    { intro pprime,
      apply char_p.eq R,
      assumption,
      exact q_prime.2, } }
end

/-- A helper lemma: the characteristic is prime if it is non-zero. -/
lemma char_prime_of_ne_zero {p : ℕ} [hp : char_p R p] (p_ne_zero : p ≠ 0) : nat.prime p :=
begin
  cases char_p.char_is_prime_or_zero R p,
  { tauto, },
  { tauto, }
end

/-- The exponential characteristic is a prime number or one. -/
theorem exp_char_is_prime_or_one (q : ℕ) [hq : exp_char R q] : 
nat.prime q ∨ q = 1 :=
begin
  by_cases q = 1,
  { exact or.inr h, },
  { cases char_p.exists R with p hp,
    haveI := hp,
    have p_ne_zero : p ≠ 0, 
    { by_contra, 
      have p_zero : p = 0, { by_contra, tauto, },
      haveI : char_p R 0 := by { rw ←p_zero, assumption, },
      have : q = 1 := exp_char_one_of_char_zero R q,
      tauto, },
    have p_eq_q : p = q, 
    { apply (char_eq_exp_char_iff R p q).mpr,
      exact char_prime_of_ne_zero R p_ne_zero, },
    cases char_p.char_is_prime_or_zero R p with pprime,
    { rw p_eq_q at pprime,
      exact or.inl pprime, },
    tauto, }
end
