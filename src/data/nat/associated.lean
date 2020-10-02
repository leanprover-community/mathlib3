/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import data.nat.prime
import algebra.associated
import tactic.omega

/-#

# Primes and irreducibles in `ℕ`

This file connects the ideas presented in `algebra.associated` with the natural numbers.

## Main results

 * `nat.prime_iff`: `nat.prime` coincides with the general definition of `prime`
 * `nat.irreducible_iff_prime`: a non-unit natural number is only divisible by `1` iff it is prime

## Tags

prime, irreducible, natural numbers,
-/

theorem nat.prime_iff {p : ℕ} : p.prime ↔ prime p :=
begin
  split; intro h,
  { refine ⟨h.ne_zero, ⟨_, λ a b, _⟩⟩,
    { rw nat.is_unit_iff, apply h.ne_one },
    { apply h.dvd_mul.1 } },
  { refine ⟨_, λ m hm, _⟩,
    { cases p, { exfalso, apply h.ne_zero rfl },
      cases p, { exfalso, apply h.ne_one rfl },
      omega },
    { cases hm with n hn,
      cases h.2.2 m n (hn ▸ dvd_refl _) with hpm hpn,
      { right, apply nat.dvd_antisymm (dvd.intro _ hn.symm) hpm },
      { left,
        cases n, { exfalso, rw [hn, mul_zero] at h, apply h.ne_zero rfl },
        apply nat.eq_of_mul_eq_mul_right (nat.succ_pos _),
        rw [← hn, one_mul],
        apply nat.dvd_antisymm hpn (dvd.intro m _),
        rw [mul_comm, hn], }, } }
end

theorem nat.irreducible_iff_prime {p : ℕ} : irreducible p ↔ prime p :=
begin
  refine ⟨λ h, _, irreducible_of_prime⟩,
  rw ← nat.prime_iff,
  refine ⟨_, λ m hm, _⟩,
  { cases p, { exfalso, apply h.ne_zero rfl },
    cases p, { exfalso, apply h.1 is_unit_one, },
    omega },
  { cases hm with n hn,
    cases h.2 m n hn with um un,
    { left, rw nat.is_unit_iff.1 um, },
    { right, rw [hn, nat.is_unit_iff.1 un, mul_one], } }
end
