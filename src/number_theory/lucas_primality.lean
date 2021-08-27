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

-- lemma zmod_order_le_card_units (hn : 1 < p) (a : zmod p) :
--   order_of a ≤ fintype.card (units (zmod p)) :=
-- begin
--   let a' : units (zmod p) := {
--     val := a,
--     inv :=
--   }
--   -- convert order_of_le_card_univ,
-- end

/-- The monoid homomorphism from the units of -/



theorem lucas_primality (a : zmod p)
  (hp : 1 < p)
  (ha : a^(p-1) = 1)
  -- (hd : (∀ d : ℕ, d ∈ (p-1).factors -> a^((p-1) / d) ≠ 1)
  (hd : (∀ d : ℕ, (nat.prime d) -> (d ∣ (p-1)) -> a^((p-1)/d) ≠ 1))
  : p.prime :=
begin
  -- TODO Use field structure on zmod p
  -- show the multiplicative group has order p-1
  have b_dvd_factor : ∃ (b : ℕ), p-1 = (order_of a) * b,
    exact exists_eq_mul_right_of_dvd (order_of_dvd_of_pow_eq_one ha),
  cases b_dvd_factor with b hb,

  have b_min_fac_dvd_p_sub_one : b.min_fac ∣ p - 1,
      have c_dvd_factor : ∃ (c : ℕ), b = c * b.min_fac ,
        refine exists_eq_mul_left_of_dvd _,
        exact nat.min_fac_dvd b,
      cases c_dvd_factor with c hc,
      rw [hc, <-mul_assoc] at hb,
      exact dvd.intro_left (order_of a * c) (eq.symm hb),

  have order_of_a : order_of a = p-1,
    { by_contra,
      -- Let f be the minimum prime factor of p-1 / order_of a
      -- f is prime
      -- f divides p-1
      -- order_of a divides p-1 / f
      apply hd (nat.min_fac b),
      apply @nat.min_fac_prime b,
      intro hb',
      rw hb' at hb,
      rw hb at h,
      simp at h,
      exact h,
      exact b_min_fac_dvd_p_sub_one,

      have hfoo : order_of a ∣ (p-1) / (b.min_fac),
        rw dvd_div_iff_mul_dvd,
        rw hb,
        rw nat.mul_dvd_mul_iff_left,
        exact nat.min_fac_dvd b,
        apply order_of_pos',
        rw is_of_fin_order_iff_pow_eq_one,
        use (p-1),
        split,
        exact sub_pos_iff_lt.mpr hp,
        exact ha,
        exact b_min_fac_dvd_p_sub_one,
        rw <-order_of_dvd_iff_pow_eq_one,
        exact hfoo, },

  -- rw <-nat.totient_prime_iff,
  -- rw nat.totient_eq_card_coprime,

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
