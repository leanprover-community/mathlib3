/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Michael Stoll
-/
import number_theory.legendre_symbol.basic
import number_theory.legendre_symbol.quadratic_char.gauss_sum

/-!
# Quadratic reciprocity.

## Main results

We prove the law of quadratic reciprocity, see `legendre_sym.quadratic_reciprocity` and
`legendre_sym.quadratic_reciprocity'`, as well as the
interpretations in terms of existence of square roots depending on the congruence mod 4,
`zmod.exists_sq_eq_prime_iff_of_mod_four_eq_one`, and
`zmod.exists_sq_eq_prime_iff_of_mod_four_eq_three`.

We also prove the supplementary laws that give conditions for when `-1` or `2`
(or `-2`) is a square modulo a prime `p`:
`legendre_sym.at_neg_one` and `zmod.exists_sq_eq_neg_one_iff` for `-1`,
`legendre_sym.at_two` and `zmod.exists_sq_eq_two_iff` for `2`,
`legendre_sym.at_neg_two` and `zmod.exists_sq_eq_neg_two_iff` for `-2`.

## Implementation notes

The proofs use results for quadratic characters on arbitrary finite fields
from `number_theory.legendre_symbol.quadratic_char.gauss_sum`, which in turn are based on
properties of quadratic Gauss sums as provided by `number_theory.legendre_symbol.gauss_sum`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol, quadratic reciprocity
-/

open nat

section values

variables {p : ℕ} [fact p.prime]

open zmod

/-!
### The value of the Legendre symbol at `2` and `-2`

See `jacobi_sym.at_two` and `jacobi_sym.at_neg_two` for the corresponding statements
for the Jacobi symbol.
-/

namespace legendre_sym

variables (hp : p ≠ 2)
include hp

/-- `legendre_sym p 2` is given by `χ₈ p`. -/
lemma at_two : legendre_sym p 2 = χ₈ p :=
by simp only [legendre_sym, card p, quadratic_char_two ((ring_char_zmod_n p).substr hp),
              int.cast_bit0, int.cast_one]

/-- `legendre_sym p (-2)` is given by `χ₈' p`. -/
lemma at_neg_two : legendre_sym p (-2) = χ₈' p :=
by simp only [legendre_sym, card p, quadratic_char_neg_two ((ring_char_zmod_n p).substr hp),
              int.cast_bit0, int.cast_one, int.cast_neg]

end legendre_sym

namespace zmod

variables (hp : p ≠ 2)
include hp

/-- `2` is a square modulo an odd prime `p` iff `p` is congruent to `1` or `7` mod `8`. -/
lemma exists_sq_eq_two_iff : is_square (2 : zmod p) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
begin
  rw [finite_field.is_square_two_iff, card p],
  have h₁ := prime.mod_two_eq_one_iff_ne_two.mpr hp,
  rw [← mod_mod_of_dvd p (by norm_num : 2 ∣ 8)] at h₁,
  have h₂ := mod_lt p (by norm_num : 0 < 8),
  revert h₂ h₁,
  generalize hm : p % 8 = m, unfreezingI {clear_dependent p},
  dec_trivial!,
end

/-- `-2` is a square modulo an odd prime `p` iff `p` is congruent to `1` or `3` mod `8`. -/
lemma exists_sq_eq_neg_two_iff : is_square (-2 : zmod p) ↔ p % 8 = 1 ∨ p % 8 = 3 :=
begin
  rw [finite_field.is_square_neg_two_iff, card p],
  have h₁ := prime.mod_two_eq_one_iff_ne_two.mpr hp,
  rw [← mod_mod_of_dvd p (by norm_num : 2 ∣ 8)] at h₁,
  have h₂ := mod_lt p (by norm_num : 0 < 8),
  revert h₂ h₁,
  generalize hm : p % 8 = m, unfreezingI {clear_dependent p},
  dec_trivial!,
end

end zmod

end values

section reciprocity

/-!
### The Law of Quadratic Reciprocity

See `jacobi_sym.quadratic_reciprocity` and variants for a version of Quadratic Reciprocity
for the Jacobi symbol.
-/

variables {p q : ℕ} [fact p.prime] [fact q.prime]

namespace legendre_sym

open zmod

/-- The Law of Quadratic Reciprocity: if `p` and `q` are distinct odd primes, then
`(q / p) * (p / q) = (-1)^((p-1)(q-1)/4)`. -/
theorem quadratic_reciprocity (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
  legendre_sym q p * legendre_sym p q = (-1) ^ ((p / 2) * (q / 2)) :=
begin
  have hp₁ := (prime.eq_two_or_odd $ fact.out p.prime).resolve_left hp,
  have hq₁ := (prime.eq_two_or_odd $ fact.out q.prime).resolve_left hq,
  have hq₂ := (ring_char_zmod_n q).substr hq,
  have h := quadratic_char_odd_prime ((ring_char_zmod_n p).substr hp) hq
              ((ring_char_zmod_n p).substr hpq),
  rw [card p] at h,
  have nc : ∀ (n r : ℕ), ((n : ℤ) : zmod r) = n := λ n r, by norm_cast,
  have nc' : (((-1) ^ (p / 2) : ℤ) : zmod q) = (-1) ^ (p / 2) := by norm_cast,
  rw [legendre_sym, legendre_sym, nc, nc, h, map_mul, mul_rotate', mul_comm (p / 2), ← pow_two,
      quadratic_char_sq_one (prime_ne_zero q p hpq.symm), mul_one, pow_mul, χ₄_eq_neg_one_pow hp₁,
      nc', map_pow, quadratic_char_neg_one hq₂, card q, χ₄_eq_neg_one_pow hq₁],
end

/-- The Law of Quadratic Reciprocity: if `p` and `q` are odd primes, then
`(q / p) = (-1)^((p-1)(q-1)/4) * (p / q)`. -/
theorem quadratic_reciprocity' (hp : p ≠ 2) (hq : q ≠ 2) :
  legendre_sym q p = (-1) ^ ((p / 2) * (q / 2)) * legendre_sym p q :=
begin
  cases eq_or_ne p q with h h,
  { substI p,
    rw [(eq_zero_iff q q).mpr (by exact_mod_cast nat_cast_self q), mul_zero] },
  { have qr := congr_arg (* legendre_sym p q) (quadratic_reciprocity hp hq h),
    have : ((q : ℤ) : zmod p) ≠ 0 := by exact_mod_cast prime_ne_zero p q h,
    simpa only [mul_assoc, ← pow_two, sq_one p this, mul_one] using qr }
end

/-- The Law of Quadratic Reciprocity: if `p` and `q` are odd primes and `p % 4 = 1`,
then `(q / p) = (p / q)`. -/
theorem quadratic_reciprocity_one_mod_four (hp : p % 4 = 1) (hq : q ≠ 2) :
  legendre_sym q p = legendre_sym p q :=
by rw [quadratic_reciprocity' (prime.mod_two_eq_one_iff_ne_two.mp
                                             (odd_of_mod_four_eq_one hp)) hq,
       pow_mul, neg_one_pow_div_two_of_one_mod_four hp, one_pow, one_mul]

/-- The Law of Quadratic Reciprocity: if `p` and `q` are primes that are both congruent
to `3` mod `4`, then `(q / p) = -(p / q)`. -/
theorem quadratic_reciprocity_three_mod_four (hp : p % 4 = 3) (hq : q % 4 = 3):
  legendre_sym q p = -legendre_sym p q :=
let nop := @neg_one_pow_div_two_of_three_mod_four in begin
  rw [quadratic_reciprocity', pow_mul, nop hp, nop hq, neg_one_mul];
  rwa [← prime.mod_two_eq_one_iff_ne_two, odd_of_mod_four_eq_three],
end

end legendre_sym

namespace zmod

open legendre_sym

/-- If `p` and `q` are odd primes and `p % 4 = 1`, then `q` is a square mod `p` iff
`p` is a square mod `q`. -/
lemma exists_sq_eq_prime_iff_of_mod_four_eq_one (hp1 : p % 4 = 1) (hq1 : q ≠ 2) :
  is_square (q : zmod p) ↔ is_square (p : zmod q) :=
begin
  cases eq_or_ne p q with h h,
  { substI p },
  { rw [← eq_one_iff' p (prime_ne_zero p q h), ← eq_one_iff' q (prime_ne_zero q p h.symm),
        quadratic_reciprocity_one_mod_four hp1 hq1], }
end

/-- If `p` and `q` are distinct primes that are both congruent to `3` mod `4`, then `q` is
a square mod `p` iff `p` is a nonsquare mod `q`. -/
lemma exists_sq_eq_prime_iff_of_mod_four_eq_three (hp3 : p % 4 = 3) (hq3 : q % 4 = 3)
  (hpq : p ≠ q) :
  is_square (q : zmod p) ↔ ¬ is_square (p : zmod q) :=
by rw [← eq_one_iff' p (prime_ne_zero p q hpq), ← eq_neg_one_iff' q,
       quadratic_reciprocity_three_mod_four hp3 hq3, neg_inj]

end zmod

end reciprocity
