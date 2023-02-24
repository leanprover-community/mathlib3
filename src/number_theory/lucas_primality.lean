/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import data.fintype.basic
import group_theory.order_of_element
import tactic.zify
import data.nat.totient

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
- Integrate Pratt primality certificates into the norm_num primality verifier

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
  have h0 : p ≠ 0, { rintro ⟨⟩, exact hd 2 nat.prime_two (dvd_zero _) (pow_zero _) },
  have h1 : p ≠ 1, { rintro ⟨⟩, exact hd 2 nat.prime_two (dvd_zero _) (pow_zero _) },
  have hp1 : 1 < p := lt_of_le_of_ne h0.bot_lt h1.symm,
  have order_of_a : order_of a = p-1,
  { apply order_of_eq_of_pow_and_pow_div_prime _ ha hd,
    exact tsub_pos_of_lt hp1, },
  haveI : ne_zero p := ⟨h0⟩,
  rw nat.prime_iff_card_units,
  -- Prove cardinality of `units` of `zmod p` is both `≤ p-1` and `≥ p-1`
  refine le_antisymm (nat.card_units_zmod_lt_sub_one hp1) _,
  have hp' : p - 2 + 1 = p - 1 := tsub_add_eq_add_tsub hp1,
  let a' : (zmod p)ˣ := units.mk_of_mul_eq_one a (a ^ (p-2)) (by rw [←pow_succ, hp', ha]),
  calc p - 1 = order_of a : order_of_a.symm
  ... = order_of a' : order_of_injective (units.coe_hom (zmod p)) units.ext a'
  ... ≤ fintype.card (zmod p)ˣ : order_of_le_card_univ,
end
