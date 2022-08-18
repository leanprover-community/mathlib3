/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Michael Stoll
-/
import number_theory.legendre_symbol.gauss_eisenstein_lemmas
import number_theory.legendre_symbol.quadratic_char

/-!
# Legendre symbol and quadratic reciprocity.

This file contains results about quadratic residues modulo a prime number.

We define the Legendre symbol `(a / p)` as `legendre_sym p a`.
Note the order of arguments! The advantage of this form is that then `legendre_sym p`
is a multiplicative map.

The main results are the law of quadratic reciprocity, `quadratic_reciprocity`, as well as the
interpretations in terms of existence of square roots depending on the congruence mod 4,
`exists_sq_eq_prime_iff_of_mod_four_eq_one`, and
`exists_sq_eq_prime_iff_of_mod_four_eq_three`.

Also proven are conditions for `-1` and `2` to be a square modulo a prime,
`legende_sym_neg_one` and `exists_sq_eq_neg_one_iff` for `-1`, and
`exists_sq_eq_two_iff` for `2`

## Implementation notes

The proof of quadratic reciprocity implemented uses Gauss' lemma and Eisenstein's lemma
-/

open finset nat char

namespace zmod

variables (p q : ℕ) [fact p.prime] [fact q.prime]

/-- Euler's Criterion: A unit `x` of `zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
lemma euler_criterion_units (x : (zmod p)ˣ) :
  (∃ y : (zmod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1 :=
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
lemma euler_criterion {a : zmod p} (ha : a ≠ 0) :
  is_square (a : zmod p) ↔ a ^ (p / 2) = 1 :=
begin
  apply (iff_congr _ (by simp [units.ext_iff])).mp (euler_criterion_units p (units.mk0 a ha)),
  simp only [units.ext_iff, sq, units.coe_mk0, units.coe_mul],
  split, { rintro ⟨y, hy⟩, exact ⟨y, hy.symm⟩ },
  { rintro ⟨y, rfl⟩,
    have hy : y ≠ 0, { rintro rfl, simpa [zero_pow] using ha, },
    refine ⟨units.mk0 y hy, _⟩, simp, }
end

lemma exists_sq_eq_neg_one_iff : is_square (-1 : zmod p) ↔ p % 4 ≠ 3 :=
by rw [finite_field.is_square_neg_one_iff, card p]

lemma mod_four_ne_three_of_sq_eq_neg_one {y : zmod p} (hy : y ^ 2 = -1) : p % 4 ≠ 3 :=
(exists_sq_eq_neg_one_iff p).1 ⟨y, hy.symm.trans (pow_two y)⟩

lemma mod_four_ne_three_of_sq_eq_neg_sq' {x y : zmod p} (hy : y ≠ 0) (hxy : x ^ 2 = - y ^ 2) :
  p % 4 ≠ 3 :=
@mod_four_ne_three_of_sq_eq_neg_one p _ (x / y) begin
  apply_fun (λ z, z / y ^ 2) at hxy,
  rwa [neg_div, ←div_pow, ←div_pow, div_self hy, one_pow] at hxy
end

lemma mod_four_ne_three_of_sq_eq_neg_sq {x y : zmod p} (hx : x ≠ 0) (hxy : x ^ 2 = - y ^ 2) :
  p % 4 ≠ 3 :=
begin
  apply_fun (λ x, -x) at hxy,
  rw neg_neg at hxy,
  exact mod_four_ne_three_of_sq_eq_neg_sq' p hx hxy.symm
end

lemma pow_div_two_eq_neg_one_or_one {a : zmod p} (ha : a ≠ 0) :
  a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 :=
begin
  cases nat.prime.eq_two_or_odd (fact.out p.prime) with hp2 hp_odd,
  { substI p, revert a ha, dec_trivial },
  rw [← mul_self_eq_one_iff, ← pow_add, ← two_mul, two_mul_odd_div_two hp_odd],
  exact pow_card_sub_one_eq_one ha
end

/-- The Legendre symbol of `a : ℤ` and a prime `p`, `legendre_sym p a`,
is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a` is a square modulo `p`
* `-1` otherwise.

Note the order of the arguments! The advantage of the order chosen here is
that `legendre_sym p` is a multiplicative function `ℤ → ℤ`.
-/
def legendre_sym (p : ℕ) [fact p.prime] (a : ℤ) : ℤ := quadratic_char (zmod p) a

/-- We have the congruence `legendre_sym p a ≡ a ^ (p / 2) mod p`. -/
lemma legendre_sym_eq_pow (p : ℕ) (a : ℤ) [hp : fact p.prime] :
  (legendre_sym p a : zmod p) = (a ^ (p / 2)) :=
begin
  cases eq_or_ne (ring_char (zmod p)) 2 with hc hc,
  { by_cases ha : (a : zmod p) = 0,
    { rw [legendre_sym, ha, quadratic_char_zero,
          zero_pow (nat.div_pos (hp.1.two_le) (succ_pos 1))],
      norm_cast, },
    { have := (ring_char_zmod_n p).symm.trans hc, -- p = 2
      substI p,
      rw [legendre_sym, quadratic_char_eq_one_of_char_two hc ha],
      revert ha,
      generalize : (a : (zmod 2)) = b, revert b, dec_trivial } },
  { convert quadratic_char_eq_pow_of_char_ne_two'' hc (a : zmod p),
    exact (card p).symm },
end

/-- If `p ∤ a`, then `legendre_sym p a` is `1` or `-1`. -/
lemma legendre_sym_eq_one_or_neg_one (p : ℕ) [fact p.prime] (a : ℤ) (ha : (a : zmod p) ≠ 0) :
  legendre_sym p a = 1 ∨ legendre_sym p a = -1 :=
quadratic_char_dichotomy ha

lemma legendre_sym_eq_neg_one_iff_not_one {a : ℤ} (ha : (a : zmod p) ≠ 0) :
  legendre_sym p a = -1 ↔ ¬ legendre_sym p a = 1 :=
quadratic_char_eq_neg_one_iff_not_one ha

/-- The Legendre symbol of `p` and `a` is zero iff `p ∣ a`. -/
lemma legendre_sym_eq_zero_iff (p : ℕ) [fact p.prime] (a : ℤ) :
  legendre_sym p a = 0 ↔ (a : zmod p) = 0 :=
quadratic_char_eq_zero_iff

@[simp] lemma legendre_sym_zero (p : ℕ) [fact p.prime] : legendre_sym p 0 = 0 :=
by rw [legendre_sym, int.cast_zero, mul_char.map_zero]

@[simp] lemma legendre_sym_one (p : ℕ) [fact p.prime] : legendre_sym p 1 = 1 :=
by rw [legendre_sym, int.cast_one, mul_char.map_one]

/-- The Legendre symbol is multiplicative in `a` for `p` fixed. -/
lemma legendre_sym_mul (p : ℕ) [fact p.prime] (a b : ℤ) :
  legendre_sym p (a * b) = legendre_sym p a * legendre_sym p b :=
begin
  rw [legendre_sym, legendre_sym, legendre_sym],
  push_cast,
  exact quadratic_char_mul (a : zmod p) b,
end

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simps] def legendre_sym_hom (p : ℕ) [fact p.prime] : ℤ →*₀ ℤ :=
{ to_fun := legendre_sym p,
  map_zero' := legendre_sym_zero p,
  map_one' := legendre_sym_one p,
  map_mul' := legendre_sym_mul p }

/-- The square of the symbol is 1 if `p ∤ a`. -/
theorem legendre_sym_sq_one (p : ℕ) [fact p.prime] (a : ℤ) (ha : (a : zmod p) ≠ 0) :
  (legendre_sym p a)^2 = 1 :=
quadratic_char_sq_one ha

/-- The Legendre symbol of `a^2` at `p` is 1 if `p ∤ a`. -/
theorem legendre_sym_sq_one'  (p : ℕ) [fact p.prime] (a : ℤ) (ha : (a : zmod p) ≠ 0) :
  legendre_sym p (a ^ 2) = 1 :=
by exact_mod_cast quadratic_char_sq_one' ha

/-- The Legendre symbol depends only on `a` mod `p`. -/
theorem legendre_sym_mod (p : ℕ) [fact p.prime] (a : ℤ) :
  legendre_sym p a = legendre_sym p (a % p) :=
by simp only [legendre_sym, int_cast_mod]


/-- Gauss' lemma. The legendre symbol can be computed by considering the number of naturals less
  than `p/2` such that `(a * x) % p > p / 2` -/
lemma gauss_lemma {a : ℤ} (hp : p ≠ 2) (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym p a = (-1) ^ ((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card :=
begin
  haveI hp' : fact (p % 2 = 1) := ⟨nat.prime.mod_two_eq_one_iff_ne_two.mpr hp⟩,
  have : (legendre_sym p a : zmod p) = (((-1)^((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card : ℤ) : zmod p) :=
    by { rw [legendre_sym_eq_pow, legendre_symbol.gauss_lemma_aux p ha0]; simp },
  cases legendre_sym_eq_one_or_neg_one p a ha0;
  cases neg_one_pow_eq_or ℤ ((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card;
  simp [*, ne_neg_self p one_ne_zero, (ne_neg_self p one_ne_zero).symm] at *
end

/-- When `p ∤ a`, then `legendre_sym p a = 1` iff `a` is a square mod `p`. -/
lemma legendre_sym_eq_one_iff {a : ℤ} (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym p a = 1 ↔ is_square (a : zmod p) :=
quadratic_char_one_iff_is_square ha0

/-- `legendre_sym p a = -1` iff`a` is a nonsquare mod `p`. -/
lemma legendre_sym_eq_neg_one_iff {a : ℤ} :
  legendre_sym p a = -1 ↔ ¬ is_square (a : zmod p) :=
quadratic_char_neg_one_iff_not_is_square

/-- The number of square roots of `a` modulo `p` is determined by the Legendre symbol. -/
lemma legendre_sym_card_sqrts (hp : p ≠ 2) (a : ℤ) :
  ↑{x : zmod p | x^2 = a}.to_finset.card = legendre_sym p a + 1 :=
quadratic_char_card_sqrts (ne_of_eq_of_ne (ring_char_zmod_n p) hp) a

/-- `legendre_sym p (-1)` is given by `χ₄ p`. -/
lemma legendre_sym_neg_one (hp : p ≠ 2) : legendre_sym p (-1) = χ₄ p :=
begin
  have h₁ := quadratic_char_neg_one (ne_of_eq_of_ne (ring_char_zmod_n p) hp),
  rw card p at h₁,
  exact_mod_cast h₁,
end

open_locale big_operators

lemma eisenstein_lemma (hp : p ≠ 2) {a : ℕ} (ha1 : a % 2 = 1) (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym p a = (-1)^∑ x in Ico 1 (p / 2).succ, (x * a) / p :=
begin
  haveI hp' : fact (p % 2 = 1) := ⟨nat.prime.mod_two_eq_one_iff_ne_two.mpr hp⟩,
  have ha0' : ((a : ℤ) : zmod p) ≠ 0 := by { norm_cast, exact ha0 },
  rw [neg_one_pow_eq_pow_mod_two, gauss_lemma p hp ha0', neg_one_pow_eq_pow_mod_two,
      (by norm_cast : ((a : ℤ) : zmod p) = (a : zmod p)),
      show _ = _, from legendre_symbol.eisenstein_lemma_aux p ha1 ha0]
end

/-- **Quadratic reciprocity theorem** -/
theorem quadratic_reciprocity (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
  legendre_sym q p * legendre_sym p q = (-1) ^ ((p / 2) * (q / 2)) :=
begin
  have h := quadratic_char_odd_prime (ne_of_eq_of_ne (ring_char_zmod_n p) hp) hq
              (ne_of_eq_of_ne (ring_char_zmod_n p) hpq),
  rw [card p] at h,
  have nc : ∀ (n r : ℕ), ((n : ℤ) : zmod r) = n := by {intros n r, norm_cast},
  rw [legendre_sym, legendre_sym, nc, nc, h, map_mul, mul_rotate', ← pow_two,
      quadratic_char_sq_one, mul_one],
  have := nat.odd_mod_four_iff.mp ((nat.prime.eq_two_or_odd (fact.out p.prime)).resolve_left hp),
  sorry
end

lemma legendre_sym_two (hp : p ≠ 2) : legendre_sym p 2 = χ₈ p :=
begin
  have h := quadratic_char_two (ne_of_eq_of_ne (ring_char_zmod_n p) hp),
  rw [card p] at h,
  rw [legendre_sym],
  exact_mod_cast h,
end

lemma exists_sq_eq_two_iff (hp : p ≠ 2) : is_square (2 : zmod p) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
begin
  rw [finite_field.is_square_two_iff, card p],
  have h₁ := nat.prime.mod_two_eq_one_iff_ne_two.mpr hp,
  rw [← nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 8)] at h₁,
  have h₂ := mod_lt p (by norm_num : 0 < 8),
  revert h₂ h₁,
  generalize hm : p % 8 = m, unfreezingI {clear_dependent p},
  dec_trivial!,
end

lemma exists_sq_eq_prime_iff_of_mod_four_eq_one (hp1 : p % 4 = 1) (hq1 : q ≠ 2) :
  is_square (q : zmod p) ↔ is_square (p : zmod q) :=
if hpq : p = q then by substI hpq else
have h1 : ((p / 2) * (q / 2)) % 2 = 0,
  from dvd_iff_mod_eq_zero.1
    (dvd_mul_of_dvd_left (dvd_iff_mod_eq_zero.2 $
    by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp1]; refl) _),
begin
  have hp_odd : p ≠ 2 := by { by_contra, simp [h] at hp1, norm_num at hp1, },
  have hpq0 : ((p : ℤ) : zmod q) ≠ 0 := by exact_mod_cast prime_ne_zero q p (ne.symm hpq),
  have hqp0 : ((q : ℤ) : zmod p) ≠ 0 := by exact_mod_cast prime_ne_zero p q hpq,
  have := quadratic_reciprocity p q hp_odd hq1 hpq,
  rw [neg_one_pow_eq_pow_mod_two, h1, pow_zero] at this,
  rw [(by norm_cast : (p : zmod q) = (p : ℤ)), (by norm_cast : (q : zmod p) = (q : ℤ)),
       ← legendre_sym_eq_one_iff _ hpq0, ← legendre_sym_eq_one_iff _ hqp0],
  cases (legendre_sym_eq_one_or_neg_one p q hqp0) with h h,
  { simp only [h, eq_self_iff_true, true_iff, mul_one] at this ⊢,
    exact this, },
  { simp only [h, mul_neg, mul_one] at this ⊢,
    rw eq_neg_of_eq_neg this.symm, },
end

lemma exists_sq_eq_prime_iff_of_mod_four_eq_three (hp3 : p % 4 = 3)
  (hq3 : q % 4 = 3) (hpq : p ≠ q) : is_square (q : zmod p) ↔ ¬ is_square (p : zmod q) :=
have h1 : ((p / 2) * (q / 2)) % 2 = 1,
  from nat.odd_mul_odd
    (by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp3]; refl)
    (by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hq3]; refl),
begin
  have hp_odd : p ≠ 2 := by { by_contra, simp [h] at hp3, norm_num at hp3, },
  have hq_odd : q ≠ 2 := by { by_contra, simp [h] at hq3, norm_num at hq3, },
  have hpq0 : ((p : ℤ) : zmod q) ≠ 0 := by exact_mod_cast prime_ne_zero q p (ne.symm hpq),
  have hqp0 : ((q : ℤ) : zmod p) ≠ 0 := by exact_mod_cast prime_ne_zero p q hpq,
  have := quadratic_reciprocity p q hp_odd hq_odd hpq,
  rw [neg_one_pow_eq_pow_mod_two, h1, pow_one] at this,
  rw [(by norm_cast : (p : zmod q) = (p : ℤ)), (by norm_cast : (q : zmod p) = (q : ℤ)),
       ← legendre_sym_eq_one_iff _ hpq0, ← legendre_sym_eq_one_iff _ hqp0],
  cases (legendre_sym_eq_one_or_neg_one q p hpq0) with h h,
  { simp only [h, eq_self_iff_true, not_true, iff_false, one_mul] at this ⊢,
    simp only [this],
    norm_num, },
  { simp only [h, neg_mul, one_mul, neg_inj] at this ⊢,
    simp only [this, eq_self_iff_true, true_iff],
    norm_num, },
end

end zmod
