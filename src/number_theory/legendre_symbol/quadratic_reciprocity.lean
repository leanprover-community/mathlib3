/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import field_theory.finite.basic
import data.zmod.basic
import data.nat.parity
import number_theory.legendre_symbol.gauss_eisenstein_lemmas

/-!
# Quadratic reciprocity.

This file contains results about quadratic residues modulo a prime number.

We define the Legendre symbol `(a / p)` as `legendre_sym p a`.
Note the order of arguments! The advantage of this form is that then `legendre_sym p`
is a multiplicative map.

The main results are the law of quadratic reciprocity, `quadratic_reciprocity`, as well as the
interpretations in terms of existence of square roots depending on the congruence mod 4,
`exists_sq_eq_prime_iff_of_mod_four_eq_one`, and
`exists_sq_eq_prime_iff_of_mod_four_eq_three`.

Also proven are conditions for `-1` and `2` to be a square modulo a prime,
`exists_sq_eq_neg_one_iff_mod_four_ne_three` and
`exists_sq_eq_two_iff`

## Implementation notes

The proof of quadratic reciprocity implemented uses Gauss' lemma and Eisenstein's lemma
-/

open function finset nat finite_field zmod
open_locale big_operators nat

namespace zmod

variables (p q : ℕ) [fact p.prime] [fact q.prime]

/-- Euler's Criterion: A unit `x` of `zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
lemma euler_criterion_units (x : (zmod p)ˣ) :
  (∃ y : (zmod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1 :=
begin
  cases nat.prime.eq_two_or_odd (fact.out p.prime) with hp2 hp_odd,
  { substI p, refine iff_of_true ⟨1, _⟩ _; apply subsingleton.elim },
  obtain ⟨g, hg⟩ := is_cyclic.exists_generator (zmod p)ˣ,
  obtain ⟨n, hn⟩ : x ∈ submonoid.powers g, { rw mem_powers_iff_mem_zpowers, apply hg },
  split,
  { rintro ⟨y, rfl⟩, rw [← pow_mul, two_mul_odd_div_two hp_odd, units_pow_card_sub_one_eq_one], },
  { subst x, assume h,
    have key : 2 * (p / 2) ∣ n * (p / 2),
    { rw [← pow_mul] at h,
      rw [two_mul_odd_div_two hp_odd, ← card_units, ← order_of_eq_card_of_forall_mem_zpowers hg],
      apply order_of_dvd_of_pow_eq_one h },
    have : 0 < p / 2 := nat.div_pos (fact.out (1 < p)) dec_trivial,
    obtain ⟨m, rfl⟩ := dvd_of_mul_dvd_mul_right this key,
    refine ⟨g ^ m, _⟩,
    rw [mul_comm, pow_mul], },
end

/-- Euler's Criterion: a nonzero `a : zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
lemma euler_criterion {a : zmod p} (ha : a ≠ 0) :
  (∃ y : zmod p, y ^ 2 = a) ↔ a ^ (p / 2) = 1 :=
begin
  apply (iff_congr _ (by simp [units.ext_iff])).mp (euler_criterion_units p (units.mk0 a ha)),
  simp only [units.ext_iff, sq, units.coe_mk0, units.coe_mul],
  split, { rintro ⟨y, hy⟩, exact ⟨y, hy⟩ },
  { rintro ⟨y, rfl⟩,
    have hy : y ≠ 0, { rintro rfl, simpa [zero_pow] using ha, },
    refine ⟨units.mk0 y hy, _⟩, simp, }
end

lemma exists_sq_eq_neg_one_iff_mod_four_ne_three :
  (∃ y : zmod p, y ^ 2 = -1) ↔ p % 4 ≠ 3 :=
begin
  cases nat.prime.eq_two_or_odd (fact.out p.prime) with hp2 hp_odd,
  { substI p, exact dec_trivial },
  haveI := fact.mk hp_odd,
  have neg_one_ne_zero : (-1 : zmod p) ≠ 0, from mt neg_eq_zero.1 one_ne_zero,
  rw [euler_criterion p neg_one_ne_zero, neg_one_pow_eq_pow_mod_two],
  cases mod_two_eq_zero_or_one (p / 2) with p_half_even p_half_odd,
  { rw [p_half_even, pow_zero, eq_self_iff_true, true_iff],
    contrapose! p_half_even with hp,
    rw [← nat.mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp],
    exact dec_trivial },
  { rw [p_half_odd, pow_one,
        iff_false_intro (ne_neg_self p one_ne_zero).symm, false_iff, not_not],
    rw [← nat.mod_mul_right_div_self, show 2 * 2 = 4, from rfl] at p_half_odd,
    rw [← nat.mod_mul_left_mod _ 2, show 2 * 2 = 4, from rfl] at hp_odd,
    have hp : p % 4 < 4, from nat.mod_lt _ dec_trivial,
    revert hp hp_odd p_half_odd,
    generalize : p % 4 = k, dec_trivial! }
end

lemma pow_div_two_eq_neg_one_or_one {a : zmod p} (ha : a ≠ 0) :
  a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 :=
begin
  cases nat.prime.eq_two_or_odd (fact.out p.prime) with hp2 hp_odd,
  { substI p, revert a ha, exact dec_trivial },
  rw [← mul_self_eq_one_iff, ← pow_add, ← two_mul, two_mul_odd_div_two hp_odd],
  exact pow_card_sub_one_eq_one ha
end

/-- The Legendre symbol of `a` and `p`, `legendre_sym p a`, is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a ^ (p / 2)` is `1` modulo `p`
   (by `euler_criterion` this is equivalent to “`a` is a square modulo `p`”);
* `-1` otherwise.

Note the order of the arguments! The advantage of the order chosen here is
that `legendre_sym p` is a multiplicative function `ℤ → ℤ`.
-/
def legendre_sym (p : ℕ) (a : ℤ) : ℤ :=
if      (a : zmod p) = 0           then  0
else if (a : zmod p) ^ (p / 2) = 1 then  1
                                   else -1

lemma legendre_sym_eq_pow (p : ℕ) (a : ℤ) [hp : fact p.prime] :
  (legendre_sym p a : zmod p) = (a ^ (p / 2)) :=
begin
  rw legendre_sym,
  by_cases ha : (a : zmod p) = 0,
  { simp only [int.cast_coe_nat, if_pos, ha,
      zero_pow (nat.div_pos (hp.1.two_le) (succ_pos 1)), int.cast_zero] },
  cases hp.1.eq_two_or_odd with hp2 hp_odd,
  { substI p,
    generalize : (a : (zmod 2)) = b, revert b, dec_trivial, },
  { haveI := fact.mk hp_odd,
    rw [if_neg ha],
    have : (-1 : zmod p) ≠ 1, from (ne_neg_self p one_ne_zero).symm,
    cases pow_div_two_eq_neg_one_or_one p ha with h h,
    { rw [if_pos h, h, int.cast_one], },
    { rw [h, if_neg this, int.cast_neg, int.cast_one], } }
end

lemma legendre_sym_eq_one_or_neg_one (p : ℕ) (a : ℤ) (ha : (a : zmod p) ≠ 0) :
  legendre_sym p a = -1 ∨ legendre_sym p a = 1 :=
begin
  unfold legendre_sym,
  split_ifs;
  simp only [*, eq_self_iff_true, or_true, true_or] at *,
end

lemma legendre_sym_eq_zero_iff (p : ℕ) (a : ℤ) :
  legendre_sym p a = 0 ↔ (a : zmod p) = 0 :=
begin
  split,
  { classical, contrapose,
    assume ha, cases legendre_sym_eq_one_or_neg_one p a ha with h h,
    all_goals { rw h, norm_num } },
  { assume ha, rw [legendre_sym, if_pos ha] }
end

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

lemma legendre_sym_eq_one_iff {a : ℤ} (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym p a = 1 ↔ (∃ b : zmod p, b ^ 2 = a) :=
begin
  rw [euler_criterion p ha0, legendre_sym, if_neg ha0],
  split_ifs,
  { simp only [h, eq_self_iff_true] },
  { simp only [h, iff_false], tauto }
end

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
theorem quadratic_reciprocity (hp1 : p ≠ 2) (hq1 : q ≠ 2) (hpq : p ≠ q) :
  legendre_sym q p * legendre_sym p q = (-1) ^ ((p / 2) * (q / 2)) :=
have hpq0 : (p : zmod q) ≠ 0, from prime_ne_zero q p hpq.symm,
have hqp0 : (q : zmod p) ≠ 0, from prime_ne_zero p q hpq,
by rw [eisenstein_lemma q hq1 (nat.prime.mod_two_eq_one_iff_ne_two.mpr hp1) hpq0,
       eisenstein_lemma p hp1 (nat.prime.mod_two_eq_one_iff_ne_two.mpr hq1) hqp0,
  ← pow_add, legendre_symbol.sum_mul_div_add_sum_mul_div_eq_mul q p hpq0, mul_comm]

lemma legendre_sym_two (hp2 : p ≠ 2) : legendre_sym p 2 = (-1) ^ (p / 4 + p / 2) :=
begin
  have hp1 := nat.prime.mod_two_eq_one_iff_ne_two.mpr hp2,
  have hp22 : p / 2 / 2 = _ := legendre_symbol.div_eq_filter_card (show 0 < 2, from dec_trivial)
    (nat.div_le_self (p / 2) 2),
  have hcard : (Ico 1 (p / 2).succ).card = p / 2, by simp,
  have hx2 : ∀ x ∈ Ico 1 (p / 2).succ, (2 * x : zmod p).val = 2 * x,
    from λ x hx, have h2xp : 2 * x < p,
        from calc 2 * x ≤ 2 * (p / 2) : mul_le_mul_of_nonneg_left
          (le_of_lt_succ $ (mem_Ico.mp hx).2) dec_trivial
        ... < _ : by conv_rhs {rw [← div_add_mod p 2, hp1]}; exact lt_succ_self _,
      by rw [← nat.cast_two, ← nat.cast_mul, val_cast_of_lt h2xp],
  have hdisj : disjoint
      ((Ico 1 (p / 2).succ).filter (λ x, p / 2 < ((2 : ℕ) * x : zmod p).val))
      ((Ico 1 (p / 2).succ).filter (λ x, x * 2 ≤ p / 2)),
    from disjoint_filter.2 (λ x hx, by simp [hx2 _ hx, mul_comm]),
  have hunion :
      ((Ico 1 (p / 2).succ).filter (λ x, p / 2 < ((2 : ℕ) * x : zmod p).val)) ∪
      ((Ico 1 (p / 2).succ).filter (λ x, x * 2 ≤ p / 2)) =
      Ico 1 (p / 2).succ,
    begin
      rw [filter_union_right],
      conv_rhs {rw [← @filter_true _ (Ico 1 (p / 2).succ)]},
      exact filter_congr (λ x hx, by simp [hx2 _ hx, lt_or_le, mul_comm])
    end,
  have hp2' := prime_ne_zero p 2 hp2,
  rw (by norm_cast : ((2 : ℕ) : zmod p) = (2 : ℤ)) at *,
  erw [gauss_lemma p hp2 hp2',
      neg_one_pow_eq_pow_mod_two, @neg_one_pow_eq_pow_mod_two _ _ (p / 4 + p / 2)],
  refine congr_arg2 _ rfl ((eq_iff_modeq_nat 2).1 _),
  rw [show 4 = 2 * 2, from rfl, ← nat.div_div_eq_div_mul, hp22, nat.cast_add,
      ← sub_eq_iff_eq_add', sub_eq_add_neg, neg_eq_self_mod_two,
      ← nat.cast_add, ← card_disjoint_union hdisj, hunion, hcard]
end

lemma exists_sq_eq_two_iff (hp1 : p ≠ 2) :
  (∃ a : zmod p, a ^ 2 = 2) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
have hp2 : ((2 : ℤ) : zmod p) ≠ 0,
  from prime_ne_zero p 2 (λ h, by simpa [h] using hp1),
have hpm4 : p % 4 = p % 8 % 4, from (nat.mod_mul_left_mod p 2 4).symm,
have hpm2 : p % 2 = p % 8 % 2, from (nat.mod_mul_left_mod p 4 2).symm,
begin
  rw [show (2 : zmod p) = (2 : ℤ), by simp, ← legendre_sym_eq_one_iff p hp2],
  erw [legendre_sym_two p hp1, neg_one_pow_eq_one_iff_even (show (-1 : ℤ) ≠ 1, from dec_trivial),
    even_add, even_div, even_div],
  have := nat.mod_lt p (show 0 < 8, from dec_trivial),
  have hp := nat.prime.mod_two_eq_one_iff_ne_two.mpr hp1,
  revert this hp,
  erw [hpm4, hpm2],
  generalize hm : p % 8 = m, unfreezingI {clear_dependent p},
  dec_trivial!,
end

lemma exists_sq_eq_prime_iff_of_mod_four_eq_one (hp1 : p % 4 = 1) (hq1 : q ≠ 2) :
  (∃ a : zmod p, a ^ 2 = q) ↔ ∃ b : zmod q, b ^ 2 = p :=
if hpq : p = q then by substI hpq else
have h1 : ((p / 2) * (q / 2)) % 2 = 0,
  from (dvd_iff_mod_eq_zero _ _).1
    (dvd_mul_of_dvd_left ((dvd_iff_mod_eq_zero _ _).2 $
    by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp1]; refl) _),
begin
  have hp_odd : p ≠ 2 := by { by_contra, simp [h] at hp1, norm_num at hp1, },
  have hpq0 : (p : zmod q) ≠ 0 := prime_ne_zero q p (ne.symm hpq),
  have hqp0 : (q : zmod p) ≠ 0 := prime_ne_zero p q hpq,
  have := quadratic_reciprocity p q hp_odd hq1 hpq,
  rw [neg_one_pow_eq_pow_mod_two, h1, legendre_sym, legendre_sym, int.cast_coe_nat,
    int.cast_coe_nat, if_neg hqp0, if_neg hpq0] at this,
  rw [euler_criterion q hpq0, euler_criterion p hqp0],
  split_ifs at this; simp *; contradiction,
end

lemma exists_sq_eq_prime_iff_of_mod_four_eq_three (hp3 : p % 4 = 3)
  (hq3 : q % 4 = 3) (hpq : p ≠ q) : (∃ a : zmod p, a ^ 2 = q) ↔ ¬∃ b : zmod q, b ^ 2 = p :=
have h1 : ((p / 2) * (q / 2)) % 2 = 1,
  from nat.odd_mul_odd
    (by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp3]; refl)
    (by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hq3]; refl),
begin
  have hp_odd : p ≠ 2 := by { by_contra, simp [h] at hp3, norm_num at hp3, },
  have hq_odd : q ≠ 2 := by { by_contra, simp [h] at hq3, norm_num at hq3, },
  have hpq0 : (p : zmod q) ≠ 0 := prime_ne_zero q p (ne.symm hpq),
  have hqp0 : (q : zmod p) ≠ 0 := prime_ne_zero p q hpq,
  have := quadratic_reciprocity p q hp_odd hq_odd hpq,
  rw [neg_one_pow_eq_pow_mod_two, h1, legendre_sym, legendre_sym, int.cast_coe_nat,
    int.cast_coe_nat, if_neg hpq0, if_neg hqp0] at this,
  rw [euler_criterion q hpq0, euler_criterion p hqp0],
  split_ifs at this; simp *; contradiction
end

end zmod
