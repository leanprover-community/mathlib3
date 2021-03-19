/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
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
variables (R : Type u)

section semiring

variables [semiring R]

/-- The definition of the exponential characteristic of a semiring. -/
class exp_char (R : Type u) [semiring R] (q : ℕ) : Prop :=
(exp_char_def : (q = 1 ∧ char_zero R) ∨ (q.prime ∧ char_p R q))

/-- The exponential characteristic is one if the characteristic is zero. -/
lemma exp_char_one_of_char_zero (q : ℕ) [hp : char_p R 0] [hq : exp_char R q] :
q = 1 :=
begin
  cases hq.exp_char_def with q_one q_prime,
  { exact q_one.1, },
  { exact false.elim (lt_irrefl _ ((hp.eq R q_prime.2).symm ▸ q_prime.1 : (0 : ℕ).prime).pos) }
end

/-- The characteristic of a domain equals the exponential characteristic iff the former is prime. -/
theorem char_eq_exp_char_iff (p q : ℕ) [hp : char_p R p] [hq : exp_char R q] :
p = q ↔ p.prime :=
begin
  unfreezingI {rcases hq.exp_char_def with ⟨rfl,q_one⟩ | q_prime},
  { split,
    { unfreezingI {rintro rfl},
      exact false.elim (one_ne_zero (hp.eq R (char_p.of_char_zero R))) },
    { intro pprime,
      rw (char_p.eq R hp infer_instance : p = 0) at pprime,
      exact false.elim (nat.not_prime_zero pprime) } },
  { split,
    { intro hpq, rw hpq, exact q_prime.1, },
    { intro _,
      exact char_p.eq R hp q_prime.2 } },
end

section nontrivial

variables [nontrivial R]

/-- The exponential characteristic is one if the characteristic is zero. -/
lemma char_zero_of_exp_char_one (p : ℕ) [hp : char_p R p] [hq : exp_char R 1] :
p = 0 :=
begin
  cases hq.exp_char_def with q_one q_prime,
  { haveI := q_one.2,
    exact char_p.eq R hp infer_instance, },
  { haveI := q_prime.2,
    exact false.elim (char_p.char_ne_one R 1 rfl), }
end

/-- The exponential characteristic is one if the characteristic is zero. -/
@[priority 100] -- see Note [lower instance priority]
instance char_zero_of_exp_char_one' [hq : exp_char R 1] : char_zero R :=
begin
  cases hq.exp_char_def,
  { exact h.2, },
  { haveI := h.2,
    exact false.elim (char_p.char_ne_one R 1 rfl), }
end

/-- The exponential characteristic is one iff the characteristic is zero. -/
theorem exp_char_one_iff_char_zero (p q : ℕ) [char_p R p] [exp_char R q] :
q = 1 ↔ p = 0 :=
begin
  split,
  { unfreezingI {rintro rfl},
    exact char_zero_of_exp_char_one R p, },
  { unfreezingI {rintro rfl},
    exact exp_char_one_of_char_zero R q, }
end

section no_zero_divisors

variable [no_zero_divisors R]

/-- A helper lemma: the characteristic is prime if it is non-zero. -/
lemma char_prime_of_ne_zero {p : ℕ} [hp : char_p R p] (p_ne_zero : p ≠ 0) : nat.prime p :=
begin
  cases char_p.char_is_prime_or_zero R p with h h,
  { exact h, },
  { contradiction, }
end

/-- The exponential characteristic is a prime number or one. -/
theorem exp_char_is_prime_or_one (q : ℕ) [hq : exp_char R q] : nat.prime q ∨ q = 1 :=
or_iff_not_imp_right.mpr $ λ h,
begin
  casesI char_p.exists R with p hp,
  have p_ne_zero : p ≠ 0,
  { intro p_zero,
    haveI : char_p R 0 := by { rwa ←p_zero },
    have : q = 1 := exp_char_one_of_char_zero R q,
    contradiction, },
  have p_eq_q : p = q := (char_eq_exp_char_iff R p q).mpr (char_prime_of_ne_zero R p_ne_zero),
  cases char_p.char_is_prime_or_zero R p with pprime,
  { rwa p_eq_q at pprime },
  { contradiction },
end

end no_zero_divisors

end nontrivial

end semiring
