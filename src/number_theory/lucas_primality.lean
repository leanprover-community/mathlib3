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
- Bonus: Show the reverse implication i.e. if a number is prime then it has a Lucas witness. See [this stackexchange](https://math.stackexchange.com/a/59911/165144) answer for proof.
- Write a tactic that uses this theorem to generate Pratt primality certificates [see](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/norm_num.20for.20real.20exponentiation/near/249615218)

## Implementation notes

It was a challenge to avoid diamonds when writing this file. Ultimately, I settled on introducing an instance of `fact (0 < p)` rather than make an instance of `fintype` on `units (zmod n)` as Mario showed how to do:

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

lemma prime_iff_card_units (p : ℕ) [hp : fact (0 < p)] :
  p.prime ↔ fintype.card (units (zmod p)) = p - 1
:=
begin
  split,
    { intro p_prime,
      haveI := fact.mk p_prime,
      convert zmod.card_units p, },
    { intro h,
      rw zmod.card_units_eq_totient at h,
      rw nat.totient_eq_iff_prime at h,
      exact h,
      exact hp.1, },
end


example (a b c : ℕ) (h : a ∣ b) : a * c ∣ b * c :=
begin
  exact mul_dvd_mul_right h c
  -- cases exists_eq_mul_left_of_dvd h with d h',
  -- rw h',
  -- rw mul_assoc,
  -- exact dvd_mul_left (a * c) d,
end


lemma dvd_div_iff_mul_dvd (a b c : ℕ) (a_dvd_b : a ∣ b) : c ∣ b / a ↔ c * a ∣ b :=
begin
  split,
  {
    intro h,
    cases exists_eq_mul_left_of_dvd h with d h',
    have h'' : b = d * c * a,
      exact nat.eq_mul_of_div_eq_left a_dvd_b h',
    rw h'',
    rw mul_assoc,
    exact dvd_mul_left (c * a) d,
  },
  {
    intro h,
    cases exists_eq_mul_left_of_dvd h with d h',
    rw h',
    rw nat.mul_div_assoc,
    rw nat.mul_div_assoc,
    by_cases a = 0,
    rw h,
    simp,
    have : 0 < a,
      exact zero_lt_iff.mpr h,
    have : a / a = 1,
      {
        exact nat.div_self this,
      },
    rw this,
    simp,
    exact dvd_mul_left a c,

  },

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
def unit_hom : (units (zmod p)) →* (zmod p) :=
{
  (@units.has_coe (zmod p) _),
  begin

  end,
  begin

  end,
}



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
        sorry,
      let a' : units (zmod p) := {
        val := a,
        inv := a ^ (p - 2),
        val_inv := begin rw <-pow_succ, rw hp', rw ha, end,
        inv_val := begin rw <-pow_succ', rw hp', rw ha, end,
      },
      have a_coe : a = a',
        { unfold_coes, },
      have order_of_a' : order_of a' = p-1,
        {
          rw <-order_of_a,
          rw a_coe,
          rw order_of_injective units.has_coe.coe,
        },
      rw <-order_of_a',
      apply order_of_le_card_univ,
      -- apply zmod_order_le_card_units,
      -- exact hp,
    },
end
