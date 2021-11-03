/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bolton Bailey
-/
import data.zmod.basic
import data.fintype.basic
import field_theory.finite.basic
import group_theory.order_of_element

/-!
# The Lucas test for primes.

This file implements the Lucas test for primes (not to be confused with the Lucas-Lehmer test for
Mersenne primes). A number `a` witnesses that `n` is prime if `a` has order `n-1` in the
multiplicative group of integers mod `n`. This is checked by verifying that `a^(n-1) = 1 (mod n)`
and `a^d ≠ 1 (mod n)` for any divisor `d | n - 1`. This test is the basis of the Pratt primality
certificate.

## TODO

- Bonus: Show the reverse implication i.e. if a number is prime then it has a Lucas witness.
  Use `units.is_cyclic` from `ring_theory/integral_domain` to show the group is cyclic.
- Write a tactic that uses this theorem to generate Pratt primality certificates
- Integrate this into the norm_num primality verifier

## Implementation notes

Note that the proof for `lucas_primality` relies on analyzing the multiplicative group
modulo `p`. Despite this, the theorem still holds vacuously for `p = 0` and `p = 1`: In these
cases, we can take `q` to be any prime and see that `hd` does not hold, since `a^((p-1)/q)` reduces
to `1`.
-/

/--
If `a^(p-1) = 1 mod p`, but `a^((p-1)/q) ≠ 1 mod p` for all prime factors `q` of `p-1`, then `p`
is prime. This is true because `a` has order `p-1` in the multiplicative group mod `p`, so this
group must itself have order `p-1`, which only happens when `p` is prime.
-/
theorem lucas_primality (p : ℕ) (a : zmod p) (ha : a^(p-1) = 1)
  (hd : ∀ q : ℕ, q.prime → q ∣ (p-1) → a^((p-1)/q) ≠ 1) : p.prime :=
begin
  have h0 : p ≠ 0,
  { exact λ h0, hd 2 nat.prime_two (by simp only [h0, zero_sub, dvd_zero]) (by simp [h0]) },
  have h1 : p ≠ 1,
  { exact λ h1, hd 2 nat.prime_two (by simp only [h1, nat.sub_self, dvd_zero]) (by simp [h1]) },
  have hp1 : 1 < p := lt_of_le_of_ne (nat.succ_le_iff.mpr (zero_lt_iff.mpr h0)) (ne.symm h1),
  have order_of_a : order_of a = p-1,
  { apply order_of_eq_of_pow_and_pow_div_prime _ ha hd,
    exact tsub_pos_of_lt hp1, },
  haveI fhp0 : fact (0 < p) := ⟨zero_lt_iff.mpr h0⟩,
  rw nat.prime_iff_card_units,
  -- Prove cardinality of `units` of `zmod p` is both `≤ p-1` and `≥ p-1`
  rw le_antisymm_iff,
  split,
  { exact nat.card_units_zmod_lt_sub_one hp1, },
  { have hp' : p - 2 + 1 = p - 1,
    { apply eq.symm,
      rw [nat.sub_eq_iff_eq_add, add_assoc, one_add_one_eq_two, ←nat.sub_eq_iff_eq_add],
      linarith,
      linarith, },
    let a' : units (zmod p) := units.mk_of_mul_eq_one a (a ^ (p-2)) (by rw [←pow_succ, hp', ha]),
    have a_coe : a = units.coe_hom (zmod p) a',
    { unfold_coes, simp, },
    have order_of_a' : order_of a' = p-1,
    { rw [←order_of_a, a_coe, order_of_injective (@units.coe_hom (zmod p) _)],
      exact units.ext, },
    rw ←order_of_a',
    apply order_of_le_card_univ, },
end
