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

-/


-- TODO Mario says this can be made computable
noncomputable instance units_zmod.fintype : Π n, fintype (units (zmod n))
| 0     := units_int.fintype
| (n+1) := units.fintype


lemma prime_iff_card_units (p : ℕ) (hp : 0 < p) :
  p.prime ↔ fintype.card (units (zmod p)) = p - 1
:=
begin
  split,
    { intro p_prime,
      haveI := fact.mk p_prime,
      convert zmod.card_units p, },
    { haveI := fact.mk hp,
      intro h,
      replace h : @fintype.card (units (zmod p)) (units.fintype) = p - 1,
      { convert h },
      rw zmod.card_units_eq_totient at h,
      rw nat.totient_prime_iff at h,
      exact h,
      exact hp, },
end


lemma foobar (a b c : ℕ) (a_dvd_b : a ∣ b) : c ∣ b / a ↔ c * a ∣ b :=
begin
  sorry,
end

lemma zmod_order_le_card_units (n : ℕ) (hn : 1 < n) (a : zmod n) :
  order_of a ≤ fintype.card (units (zmod n)) :=
begin
  sorry,
end

theorem lucas_primality (p : ℕ) (a : zmod p)
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
        rw foobar,
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



  sorry,
end
