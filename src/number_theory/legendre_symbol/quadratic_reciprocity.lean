/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Michael Stoll
-/
import number_theory.legendre_symbol.quadratic_char

/-!
# Legendre symbol and quadratic reciprocity.

This file contains results about quadratic residues modulo a prime number.

We define the Legendre symbol $\Bigl(\frac{a}{p}\Bigr)$ as `legendre_sym p a`.
Note the order of arguments! The advantage of this form is that then `legendre_sym p`
is a multiplicative map.

The Legendre symbol is used to define the Jacobi symbol, `jacobi_sym a b`, for integers `a`
and (odd) natural numbers `b`, which extends the Legendre symbol.

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
from `number_theory.legendre_symbol.quadratic_char`, which in turn are based on
properties of quadratic Gauss sums as provided by `number_theory.legendre_symbol.gauss_sum`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol, quadratic reciprocity
-/

open nat

section euler

namespace zmod

variables (p : ℕ) [fact p.prime]

/-- Euler's Criterion: A unit `x` of `zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
lemma euler_criterion_units (x : (zmod p)ˣ) : (∃ y : (zmod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1 :=
begin
  by_cases hc : p = 2,
  { substI hc,
    simp only [eq_iff_true_of_subsingleton, exists_const], },
  { have h₀ := finite_field.unit_is_square_iff (by rwa ring_char_zmod_n) x,
    have hs : (∃ y : (zmod p)ˣ, y ^ 2 = x) ↔ is_square(x) :=
    by { rw is_square_iff_exists_sq x,
         simp_rw eq_comm, },
    rw hs,
    rwa card p at h₀, },
end

/-- Euler's Criterion: a nonzero `a : zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
lemma euler_criterion {a : zmod p} (ha : a ≠ 0) : is_square (a : zmod p) ↔ a ^ (p / 2) = 1 :=
begin
  apply (iff_congr _ (by simp [units.ext_iff])).mp (euler_criterion_units p (units.mk0 a ha)),
  simp only [units.ext_iff, sq, units.coe_mk0, units.coe_mul],
  split, { rintro ⟨y, hy⟩, exact ⟨y, hy.symm⟩ },
  { rintro ⟨y, rfl⟩,
    have hy : y ≠ 0, { rintro rfl, simpa [zero_pow] using ha, },
    refine ⟨units.mk0 y hy, _⟩, simp, }
end

/-- If `a : zmod p` is nonzero, then `a^(p/2)` is either `1` or `-1`. -/
lemma pow_div_two_eq_neg_one_or_one {a : zmod p} (ha : a ≠ 0) :
  a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 :=
begin
  cases prime.eq_two_or_odd (fact.out p.prime) with hp2 hp_odd,
  { substI p, revert a ha, dec_trivial },
  rw [← mul_self_eq_one_iff, ← pow_add, ← two_mul, two_mul_odd_div_two hp_odd],
  exact pow_card_sub_one_eq_one ha
end

end zmod

end euler

section legendre

/-!
### Definition of the Legendre symbol and basic properties
-/

open zmod

variables (p : ℕ) [fact p.prime]

/-- The Legendre symbol of `a : ℤ` and a prime `p`, `legendre_sym p a`,
is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a` is a nonzero square modulo `p`
* `-1` otherwise.

Note the order of the arguments! The advantage of the order chosen here is
that `legendre_sym p` is a multiplicative function `ℤ → ℤ`.
-/
def legendre_sym (a : ℤ) : ℤ := quadratic_char (zmod p) a

namespace legendre_sym

/-- We have the congruence `legendre_sym p a ≡ a ^ (p / 2) mod p`. -/
lemma eq_pow (a : ℤ) : (legendre_sym p a : zmod p) = a ^ (p / 2) :=
begin
  cases eq_or_ne (ring_char (zmod p)) 2 with hc hc,
  { by_cases ha : (a : zmod p) = 0,
    { rw [legendre_sym, ha, quadratic_char_zero,
          zero_pow (nat.div_pos (fact.out p.prime).two_le (succ_pos 1))],
      norm_cast, },
    { have := (ring_char_zmod_n p).symm.trans hc, -- p = 2
      substI p,
      rw [legendre_sym, quadratic_char_eq_one_of_char_two hc ha],
      revert ha,
      generalize : (a : zmod 2) = b, revert b, dec_trivial } },
  { convert quadratic_char_eq_pow_of_char_ne_two' hc (a : zmod p),
    exact (card p).symm },
end

/-- If `p ∤ a`, then `legendre_sym p a` is `1` or `-1`. -/
lemma eq_one_or_neg_one {a : ℤ} (ha : (a : zmod p) ≠ 0) :
  legendre_sym p a = 1 ∨ legendre_sym p a = -1 :=
quadratic_char_dichotomy ha

lemma eq_neg_one_iff_not_one {a : ℤ} (ha : (a : zmod p) ≠ 0) :
  legendre_sym p a = -1 ↔ ¬ legendre_sym p a = 1 :=
quadratic_char_eq_neg_one_iff_not_one ha

/-- The Legendre symbol of `p` and `a` is zero iff `p ∣ a`. -/
lemma eq_zero_iff (a : ℤ) : legendre_sym p a = 0 ↔ (a : zmod p) = 0 :=
quadratic_char_eq_zero_iff

@[simp] lemma at_zero : legendre_sym p 0 = 0 :=
by rw [legendre_sym, int.cast_zero, mul_char.map_zero]

@[simp] lemma at_one : legendre_sym p 1 = 1 :=
by rw [legendre_sym, int.cast_one, mul_char.map_one]

/-- The Legendre symbol is multiplicative in `a` for `p` fixed. -/
protected
lemma mul (a b : ℤ) : legendre_sym p (a * b) = legendre_sym p a * legendre_sym p b :=
by simp only [legendre_sym, int.cast_mul, map_mul]

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simps] def hom : ℤ →*₀ ℤ :=
{ to_fun := legendre_sym p,
  map_zero' := at_zero p,
  map_one' := at_one p,
  map_mul' := legendre_sym.mul p }

/-- The square of the symbol is 1 if `p ∤ a`. -/
theorem sq_one {a : ℤ} (ha : (a : zmod p) ≠ 0) : (legendre_sym p a) ^ 2 = 1 :=
quadratic_char_sq_one ha

/-- The Legendre symbol of `a^2` at `p` is 1 if `p ∤ a`. -/
theorem sq_one' {a : ℤ} (ha : (a : zmod p) ≠ 0) : legendre_sym p (a ^ 2) = 1 :=
by exact_mod_cast quadratic_char_sq_one' ha

/-- The Legendre symbol depends only on `a` mod `p`. -/
protected
theorem mod (a : ℤ) : legendre_sym p a = legendre_sym p (a % p) :=
by simp only [legendre_sym, int_cast_mod]

/-- When `p ∤ a`, then `legendre_sym p a = 1` iff `a` is a square mod `p`. -/
lemma eq_one_iff {a : ℤ} (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym p a = 1 ↔ is_square (a : zmod p) :=
quadratic_char_one_iff_is_square ha0

lemma eq_one_iff' {a : ℕ} (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym p a = 1 ↔ is_square (a : zmod p) :=
by {rw eq_one_iff, norm_cast, exact_mod_cast ha0}

/-- `legendre_sym p a = -1` iff `a` is a nonsquare mod `p`. -/
lemma eq_neg_one_iff {a : ℤ} : legendre_sym p a = -1 ↔ ¬ is_square (a : zmod p) :=
quadratic_char_neg_one_iff_not_is_square

lemma eq_neg_one_iff' {a : ℕ} : legendre_sym p a = -1 ↔ ¬ is_square (a : zmod p) :=
by {rw eq_neg_one_iff, norm_cast}

/-- The number of square roots of `a` modulo `p` is determined by the Legendre symbol. -/
lemma card_sqrts (hp : p ≠ 2) (a : ℤ) :
  ↑{x : zmod p | x^2 = a}.to_finset.card = legendre_sym p a + 1 :=
quadratic_char_card_sqrts ((ring_char_zmod_n p).substr hp) a

end legendre_sym

end legendre

section values

/-!
### The value of the Legendre symbol at `-1`

See `jacobi_sym.at_neg_one` for the corresponding statement for the Jacobi symbol.
-/

variables {p : ℕ} [fact p.prime]

open zmod

/-- `legendre_sym p (-1)` is given by `χ₄ p`. -/
lemma legendre_sym.at_neg_one (hp : p ≠ 2) : legendre_sym p (-1) = χ₄ p :=
by simp only [legendre_sym, card p, quadratic_char_neg_one ((ring_char_zmod_n p).substr hp),
              int.cast_neg, int.cast_one]

namespace zmod

/-- `-1` is a square in `zmod p` iff `p` is not congruent to `3` mod `4`. -/
lemma exists_sq_eq_neg_one_iff : is_square (-1 : zmod p) ↔ p % 4 ≠ 3 :=
by rw [finite_field.is_square_neg_one_iff, card p]

lemma mod_four_ne_three_of_sq_eq_neg_one {y : zmod p} (hy : y ^ 2 = -1) : p % 4 ≠ 3 :=
exists_sq_eq_neg_one_iff.1 ⟨y, hy ▸ pow_two y⟩

/-- If two nonzero squares are negatives of each other in `zmod p`, then `p % 4 ≠ 3`. -/
lemma mod_four_ne_three_of_sq_eq_neg_sq' {x y : zmod p} (hy : y ≠ 0) (hxy : x ^ 2 = - y ^ 2) :
  p % 4 ≠ 3 :=
@mod_four_ne_three_of_sq_eq_neg_one p _ (x / y) begin
  apply_fun (λ z, z / y ^ 2) at hxy,
  rwa [neg_div, ←div_pow, ←div_pow, div_self hy, one_pow] at hxy
end

lemma mod_four_ne_three_of_sq_eq_neg_sq {x y : zmod p} (hx : x ≠ 0) (hxy : x ^ 2 = - y ^ 2) :
  p % 4 ≠ 3 :=
mod_four_ne_three_of_sq_eq_neg_sq' hx (neg_eq_iff_eq_neg.mpr hxy).symm

end zmod

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
