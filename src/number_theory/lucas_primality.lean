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

- Implement the test
- Bonus: Show the reverse implication i.e. if a number is prime then it has a Lucas witness.
  See [this stackexchange](https://math.stackexchange.com/a/59911/165144) answer for proof.
- Write a tactic that uses this theorem to generate Pratt primality certificates
- Integrate this into the norm_num primality verifier

## Implementation notes

It was a challenge to avoid diamonds when writing this file. Ultimately, I settled on introducing
an instance of `fact (0 < p)` rather than make an instance of `fintype` on `units (zmod n)` as
Mario showed how to do:

```
noncomputable instance units_zmod.fintype : Π n, fintype (units (zmod n))
| 0     := units_int.fintype
| (n+1) := units.fintype
```
Note that Mario also remarked this could be made computable.

-/

variables (p : ℕ) [fact (0 < p)]

lemma card_units_zmod_lt_sub_one (hp : 1 < p) : fintype.card (units (zmod p)) ≤ p - 1 :=
begin
  rw zmod.card_units_eq_totient p,
  exact nat.le_pred_of_lt (nat.totient_lt p hp),
end

lemma prime_iff_card_units (p : ℕ) [fact (0 < p)] :
  p.prime ↔ fintype.card (units (zmod p)) = p - 1 :=
by rw [zmod.card_units_eq_totient, nat.totient_eq_iff_prime (fact.out (0 < p))]

lemma dvd_iff_exists_eq_mul_left (a b : ℕ) :
a ∣ b ↔ ∃ c, b = c * a
:=
begin
  split,
    exact exists_eq_mul_left_of_dvd,
    intro h,
    cases h with c h',
    exact dvd.intro_left c (eq.symm h'),
end

lemma dvd_div_iff_mul_dvd (a b c : ℕ) (a_dvd_b : a ∣ b) : c ∣ b / a ↔ c * a ∣ b :=
begin
  by_cases ha : a = 0,
  { rw ha,
    simp only [true_iff, zero_dvd_iff, mul_zero, nat.div_zero, dvd_zero],
    rw dvd_iff_exists_eq_mul_left at a_dvd_b,
    cases a_dvd_b with c h',
    rw [h', ha],
    simp, },
  { rw [dvd_iff_exists_eq_mul_left, dvd_iff_exists_eq_mul_left],
    apply exists_congr,
    intro d,
    split,
    { intro h,
      rw [nat.eq_mul_of_div_eq_left a_dvd_b h, mul_assoc], },
    { intro h,
      rw [h, nat.mul_div_assoc, nat.mul_div_assoc, nat.div_self (zero_lt_iff.mpr ha)],
      simp,
      simp, }, },
end

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

  rw [←order_of_dvd_iff_pow_eq_one, dvd_div_iff_mul_dvd, hb, nat.mul_dvd_mul_iff_left],
  exact nat.min_fac_dvd b,
  apply order_of_pos',
  rw is_of_fin_order_iff_pow_eq_one,
  exact Exists.intro r (id ⟨sub_pos_iff_lt.mpr hp, ha⟩),
end

/--
If a^(p-1) = 1 mod p, but a^((p-1)/q) ≠ 1 mod p for all prime factors q of p-1, then p is prime.
This is true because the above condition implies that a has order p-1 in the multiplicative group
mod p, so this group must itself have order p-1, which only happens when p is prime.
-/
theorem lucas_primality (a : zmod p)
  (hp : 1 < p)
  (ha : a^(p-1) = 1)
  (hd : (∀ q : ℕ, (nat.prime q) -> (q ∣ (p-1)) -> a^((p-1)/q) ≠ 1))
  : p.prime :=
begin
  -- Let b be (p-1)/(order_of a)

  have order_of_a : order_of a = p-1,
    { apply order_from_pows p (p - 1) a _ ha hd,
      exact sub_pos_iff_lt.mpr hp, },
  rw prime_iff_card_units,
  rw le_antisymm_iff,
  split,
    {
      exact card_units_zmod_lt_sub_one p hp,
    },
    {
      have hp' : p - 2 + 1 = p - 1,
        { apply eq.symm,
          rw nat.sub_eq_iff_eq_add,
          rw add_assoc,
          norm_num,
          rw <-nat.sub_eq_iff_eq_add,
          linarith,
          linarith, },
      let a' : units (zmod p) := {
        val := a,
        inv := a ^ (p - 2),
        val_inv := begin rw <-pow_succ, rw hp', rw ha, end,
        inv_val := begin rw <-pow_succ', rw hp', rw ha, end,
      },
      have a_coe : a = units.coe_hom (zmod p) a',
        { unfold_coes, simp, },
      have order_of_a' : order_of a' = p-1,
        {
          rw <-order_of_a,
          rw a_coe,
          rw order_of_injective (@units.coe_hom (zmod p) _),
          exact units.ext,
        },
      rw <-order_of_a',
      apply order_of_le_card_univ,
      -- apply zmod_order_le_card_units,
      -- exact hp,
    },
end
