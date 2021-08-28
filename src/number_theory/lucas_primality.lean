/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import data.zmod.basic
import data.fintype.basic
import field_theory.finite.basic
import group_theory.order_of_element

/-!
# The Lucas test for primes.

This file implements the Lucas test for primes (not to be confused with the Lucas-Lehmer test for
Mersenne primes). A number a witnesses that n is prime if a has order n-1 in the multiplicative
group of integers mod n. This is checked by verifying that a^(n-1) = 1 (mod n) and a^d ≠ 1 (mod n)
for any divisor d | n. This test is the basis of the Pratt primality certificate.

## TODO

- Bonus: Show the reverse implication i.e. if a number is prime then it has a Lucas witness.
  See [this stackexchange](https://math.stackexchange.com/a/59911/165144) answer for proof.
- Write a tactic that uses this theorem to generate Pratt primality certificates
- Integrate this into the norm_num primality verifier

## Implementation notes

It was a challenge to avoid diamonds when writing this file. Ultimately, I settled on introducing
an instance of `fact (0 < p)` rather than making an instance of `fintype` on `units (zmod n)` as
Mario showed how to do:

```
noncomputable instance units_zmod.fintype : Π n, fintype (units (zmod n))
| 0     := units_int.fintype
| (n+1) := units.fintype
```
Note that Mario also remarked this could be made computable.

-/

variables (p : ℕ) [fact (0 < p)]

/--
If a^r = 1 mod p, but a^(r/q) ≠ 1 mod p for all prime factors q of r, then a has order r in the
multiplicative group mod p.
-/
theorem order_from_pows (n r : ℕ) (a : zmod n)
  (hp : 0 < r)
  (ha : a^r = 1)
  (hd : (∀ q : ℕ, (nat.prime q) -> (q ∣ r) -> a^(r/q) ≠ 1))
  : order_of a = r :=
begin
  -- Let b be r/(order_of a), and show b = 1
  cases exists_eq_mul_right_of_dvd (order_of_dvd_of_pow_eq_one ha) with b hb,
  suffices : b = 1, by simp [this, hb],
  -- If b is not one, use the minimum prime factor of b as q.
  by_contra,
  have b_min_fac_dvd_p_sub_one : b.min_fac ∣ r,
    { have c_dvd_factor : ∃ (c : ℕ), b = c * b.min_fac,
        exact exists_eq_mul_left_of_dvd b.min_fac_dvd,
      cases c_dvd_factor with c hc,
      rw [hc, ←mul_assoc] at hb,
      exact dvd.intro_left (order_of a * c) (eq.symm hb), },
  refine hd b.min_fac (nat.min_fac_prime h) b_min_fac_dvd_p_sub_one _,

  rw [←order_of_dvd_iff_pow_eq_one, nat.dvd_div_iff, hb, mul_comm, nat.mul_dvd_mul_iff_left],
  exact nat.min_fac_dvd b,
  apply order_of_pos',
  rw is_of_fin_order_iff_pow_eq_one,
  exact Exists.intro r (id ⟨sub_pos_iff_lt.mpr hp, ha⟩),
  exact b_min_fac_dvd_p_sub_one,
end

/--
If a^(p-1) = 1 mod p, but a^((p-1)/q) ≠ 1 mod p for all prime factors q of p-1, then p is prime.
This is true because a has order p-1 in the multiplicative group mod p, so this group must itself
have order p-1, which only happens when p is prime.
-/
theorem lucas_primality (a : zmod p)
  (hp : 1 < p)
  (ha : a^(p-1) = 1)
  (hd : (∀ q : ℕ, (nat.prime q) -> (q ∣ (p-1)) -> a^((p-1)/q) ≠ 1))
  : p.prime :=
begin
  have order_of_a : order_of a = p-1,
    { apply order_from_pows p (p - 1) a _ ha hd,
      exact sub_pos_iff_lt.mpr hp, },
  rw prime_iff_card_units,
  -- Prove cardinality of units of zmod p are le and ge p-1
  rw le_antisymm_iff,
  split,
    { exact card_units_zmod_lt_sub_one p hp, },
    { have hp' : p - 2 + 1 = p - 1,
        { apply eq.symm,
          rw [nat.sub_eq_iff_eq_add, add_assoc, one_add_one_eq_two, ←nat.sub_eq_iff_eq_add],
          linarith,
          linarith, },
      let a' : units (zmod p) := units.mk_of_mul_eq_one a (a ^ (p-2)) _,
      have a_coe : a = units.coe_hom (zmod p) a',
        { unfold_coes, simp, },
      have order_of_a' : order_of a' = p-1,
        { rw [←order_of_a, a_coe, order_of_injective (@units.coe_hom (zmod p) _)],
          exact units.ext, },
      rw ←order_of_a',
      apply order_of_le_card_univ,
      rw [←pow_succ, hp', ha], },
end
