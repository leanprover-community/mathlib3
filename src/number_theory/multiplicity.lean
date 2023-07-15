/-
Copyright (c) 2022 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen, Mantas Bakšys
-/
import algebra.geom_sum
import data.int.parity
import data.zmod.basic
import number_theory.padics.padic_val
import ring_theory.ideal.quotient_operations

/-!
# Multiplicity in Number Theory

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains results in number theory relating to multiplicity.

## Main statements

* `multiplicity.int.pow_sub_pow` is the lifting the exponent lemma for odd primes.
  We also prove several variations of the lemma.

## References

* [Wikipedia, *Lifting-the-exponent lemma*]
  (https://en.wikipedia.org/wiki/Lifting-the-exponent_lemma)
-/

open ideal ideal.quotient finset
open_locale big_operators

variables {R : Type*} {n : ℕ}


section comm_ring
variables [comm_ring R] {a b x y : R}


lemma dvd_geom_sum₂_iff_of_dvd_sub {x y p : R} (h : p ∣ x - y) :
  p ∣ ∑ i in range n, x ^ i * y ^ (n - 1 - i) ↔ p ∣ n * y ^ (n - 1) :=
begin
  rw [← mem_span_singleton, ← ideal.quotient.eq] at h,
  simp only [← mem_span_singleton, ← eq_zero_iff_mem, ring_hom.map_geom_sum₂, h, geom_sum₂_self,
    _root_.map_mul, map_pow, map_nat_cast]
end

lemma dvd_geom_sum₂_iff_of_dvd_sub' {x y p : R} (h : p ∣ x - y) :
  p ∣ ∑ i in range n, x ^ i * y ^ (n - 1 - i) ↔ p ∣ n * x ^ (n - 1) :=
by rw [geom_sum₂_comm, dvd_geom_sum₂_iff_of_dvd_sub]; simpa using h.neg_right

lemma dvd_geom_sum₂_self {x y : R} (h : ↑n ∣ x - y) : ↑n ∣ ∑ i in range n, x ^ i * y ^ (n - 1 - i):=
(dvd_geom_sum₂_iff_of_dvd_sub h).mpr (dvd_mul_right _ _)

lemma sq_dvd_add_pow_sub_sub (p x : R) (n : ℕ) :
  p ^ 2 ∣ (x + p) ^ n - x ^ (n - 1) * p * n - x ^ n :=
begin
  cases n,
  { simp only [pow_zero, nat.cast_zero, mul_zero, sub_zero, sub_self, dvd_zero]},
  { simp only [nat.succ_sub_succ_eq_sub, tsub_zero, nat.cast_succ, add_pow,
      finset.sum_range_succ, nat.choose_self, nat.succ_sub _, tsub_self, pow_one,
      nat.choose_succ_self_right, pow_zero, mul_one, nat.cast_zero, zero_add, nat.succ_eq_add_one],
    suffices : p ^ 2 ∣ ∑ (i : ℕ) in range n, x ^ i * p ^ (n + 1 - i) * ↑((n + 1).choose i),
    { convert this; abel },
    { apply finset.dvd_sum,
      intros y hy,
      calc p ^ 2 ∣ p ^ (n + 1 - y) : pow_dvd_pow p (le_tsub_of_add_le_left
        (by linarith [finset.mem_range.mp hy]))
      ... ∣ x ^ y * p ^ (n + 1 - y) * ↑((n + 1).choose y) : dvd_mul_of_dvd_left (dvd_mul_left _ _)
        ((n + 1).choose y) }}
end

lemma not_dvd_geom_sum₂ {p : R} (hp : prime p)
  (hxy : p ∣ x - y) (hx : ¬p ∣ x) (hn : ¬p ∣ n) :
  ¬p ∣ ∑ i in range n, x ^ i * y ^ (n - 1 - i) :=
λ h, hx $ hp.dvd_of_dvd_pow $
(hp.dvd_or_dvd $ (dvd_geom_sum₂_iff_of_dvd_sub' hxy).mp h).resolve_left hn

variables {p : ℕ} (a b)

lemma odd_sq_dvd_geom_sum₂_sub (hp : odd p) :
  ↑p ^ 2 ∣ ∑ i in range p, (a + p * b) ^ i * a ^ (p - 1 - i) - p * a ^ (p - 1) :=
begin
  have h1 : ∀ i, ↑p ^ 2 ∣ (a + ↑p * b) ^ i - (a ^ (i - 1) * (↑p * b) * ↑i + a ^ i),
  { intro i,
    calc ↑p ^ 2 ∣ (↑p * b) ^ 2 : by simp only [mul_pow, dvd_mul_right]
    ... ∣ (a + ↑p * b) ^ i - (a ^ (i - 1) * (↑p * b) * ↑i + a ^ i) :
      by simp only [sq_dvd_add_pow_sub_sub (↑p * b) a i, ← sub_sub] },
  simp_rw [← mem_span_singleton, ← ideal.quotient.eq] at *,
  calc ideal.quotient.mk (span {↑p ^ 2}) (∑ i in range p, (a + ↑p * b) ^ i * a ^ (p - 1 - i))
      = ∑ (i : ℕ) in finset.range p, mk (span {↑p ^ 2})
          ((a ^ (i - 1) * (↑p * b) * ↑i + a ^ i) * a ^ (p - 1 - i)) :
    by simp_rw [ring_hom.map_geom_sum₂, ← map_pow, h1, ← _root_.map_mul]
  ... = mk (span {↑p ^ 2}) (∑ (x : ℕ) in finset.range p,
          a ^ (x - 1) * (a ^ (p - 1 - x) * (↑p * (b * ↑x)))) +
        mk (span {↑p ^ 2}) (∑ (x : ℕ) in finset.range p, a ^ (x + (p - 1 - x))) :
    by { ring_exp,
         simp only [← pow_add, map_add, finset.sum_add_distrib, ← map_sum] }
  ... = mk (span {↑p ^ 2}) (∑ (x : ℕ) in finset.range p,
          a ^ (x - 1) * (a ^ (p - 1 - x) * (↑p * (b * ↑x)))) +
        mk (span {↑ p ^ 2}) ∑ (x : ℕ) in finset.range p, a ^ (p - 1) :
    by { rw [add_right_inj, finset.sum_congr rfl],
         intros x hx,
         rw [← nat.add_sub_assoc _ x, nat.add_sub_cancel_left],
         exact nat.le_pred_of_lt (finset.mem_range.mp hx) }
  ... = mk (span {↑p ^ 2}) (∑ (x : ℕ) in finset.range p,
          a ^ (x - 1) * (a ^ (p - 1 - x) * (↑p * (b * ↑x)))) +
        mk (span {↑ p ^ 2}) (↑p * a ^ (p - 1)) :
    by simp only [add_right_inj, finset.sum_const, finset.card_range, nsmul_eq_mul]
  ... = mk (span {↑p ^ 2}) (↑p * b * ∑ (x : ℕ) in finset.range p, a ^ (p - 2) * x) +
        mk (span {↑p ^ 2}) (↑p * a ^ (p - 1)) :
    by { simp only [finset.mul_sum, ← mul_assoc, ← pow_add],
         rw finset.sum_congr rfl,
         rintros (⟨⟩|⟨x⟩) hx,
         { rw [nat.cast_zero, mul_zero, mul_zero] },
         { have : x.succ - 1 + (p - 1 - x.succ) = p - 2,
           { rw ← nat.add_sub_assoc (nat.le_pred_of_lt (finset.mem_range.mp hx)),
             exact congr_arg nat.pred (nat.add_sub_cancel_left _ _)},
           rw this,
           ring_exp_eq }}
  ... = mk (span {↑p ^ 2}) (↑p * a ^ (p - 1)) :
    by { simp only [add_left_eq_self, ← finset.mul_sum],
         norm_cast,
         simp only [finset.sum_range_id, nat.cast_mul, _root_.map_mul,
           nat.mul_div_assoc _ (even_iff_two_dvd.mp (nat.odd.sub_odd hp odd_one))],
         ring_exp,
         simp only [← map_pow, mul_eq_zero_of_left, ideal.quotient.eq_zero_iff_mem,
           mem_span_singleton] }
end


namespace multiplicity

section integral_domain
variables [is_domain R] [@decidable_rel R (∣)]

lemma pow_sub_pow_of_prime {p : R} (hp : prime p) {x y : R} (hxy : p ∣ x - y) (hx : ¬p ∣ x)
  {n : ℕ} (hn : ¬p ∣ n) :
  multiplicity p (x ^ n - y ^ n) = multiplicity p (x - y) :=
by rw [←geom_sum₂_mul, multiplicity.mul hp,
  multiplicity_eq_zero.2 (not_dvd_geom_sum₂ hp hxy hx hn), zero_add]

variables (hp : prime (p : R)) (hp1 : odd p) (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x)
include hp hp1 hxy hx

lemma geom_sum₂_eq_one : multiplicity ↑p (∑ i in range p, x ^ i * y ^ (p - 1 - i)) = 1 :=
begin
  rw ← nat.cast_one,
  refine multiplicity.eq_coe_iff.2 ⟨_, _⟩,
  { rw pow_one,
    exact dvd_geom_sum₂_self hxy },
  rw dvd_iff_dvd_of_dvd_sub hxy at hx,
  cases hxy with k hk,
  rw [one_add_one_eq_two, eq_add_of_sub_eq' hk],
  refine mt (dvd_iff_dvd_of_dvd_sub (@odd_sq_dvd_geom_sum₂_sub _ _ y k _ hp1)).mp _,
  rw [pow_two, mul_dvd_mul_iff_left hp.ne_zero],
  exact mt hp.dvd_of_dvd_pow hx
end

lemma pow_prime_sub_pow_prime : multiplicity ↑p (x ^ p - y ^ p) = multiplicity ↑p (x - y) + 1 :=
by rw [←geom_sum₂_mul, multiplicity.mul hp, geom_sum₂_eq_one hp hp1 hxy hx, add_comm]

lemma pow_prime_pow_sub_pow_prime_pow (a : ℕ) :
  multiplicity ↑p (x ^ p ^ a - y ^ p ^ a) = multiplicity ↑p (x - y) + a :=
begin
  induction a with a h_ind,
  { rw [nat.cast_zero, add_zero, pow_zero, pow_one, pow_one] },
  rw [←nat.add_one, nat.cast_add, nat.cast_one, ←add_assoc, ←h_ind, pow_succ', pow_mul, pow_mul],
  apply pow_prime_sub_pow_prime hp hp1,
  { rw ←geom_sum₂_mul,
    exact dvd_mul_of_dvd_right hxy _ },
  { exact λ h, hx (hp.dvd_of_dvd_pow h) }
end

end integral_domain

section lifting_the_exponent
variables (hp : nat.prime p) (hp1 : odd p)
include hp hp1

/-- **Lifting the exponent lemma** for odd primes. -/
lemma int.pow_sub_pow {x y : ℤ} (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x) (n : ℕ) :
  multiplicity ↑p (x ^ n - y ^ n) = multiplicity ↑p (x - y) + multiplicity p n :=
begin
  cases n,
  { simp only [multiplicity.zero, add_top, pow_zero, sub_self] },
  have h : (multiplicity _ _).dom := finite_nat_iff.mpr ⟨hp.ne_one, n.succ_pos⟩,
  rcases eq_coe_iff.mp (part_enat.coe_get h).symm with ⟨⟨k, hk⟩, hpn⟩,
  conv_lhs { rw [hk, pow_mul, pow_mul] },
  rw nat.prime_iff_prime_int at hp,
  rw [pow_sub_pow_of_prime hp, pow_prime_pow_sub_pow_prime_pow hp hp1 hxy hx, part_enat.coe_get],
  { rw ←geom_sum₂_mul,
    exact dvd_mul_of_dvd_right hxy _ },
  { exact λ h, hx (hp.dvd_of_dvd_pow h) },
  { rw int.coe_nat_dvd,
    rintro ⟨c, rfl⟩,
    refine hpn ⟨c, _⟩,
    rwa [pow_succ', mul_assoc] }
end
lemma int.pow_add_pow {x y : ℤ} (hxy : ↑p ∣ x + y) (hx : ¬↑p ∣ x) {n : ℕ} (hn : odd n) :
  multiplicity ↑p (x ^ n + y ^ n) = multiplicity ↑p (x + y) + multiplicity p n :=
begin
  rw ←sub_neg_eq_add at hxy,
  rw [←sub_neg_eq_add, ←sub_neg_eq_add, ←odd.neg_pow hn],
  exact int.pow_sub_pow hp hp1 hxy hx n
end

lemma nat.pow_sub_pow {x y : ℕ} (hxy : p ∣ x - y) (hx : ¬p ∣ x) (n : ℕ) :
  multiplicity p (x ^ n - y ^ n) = multiplicity p (x - y) + multiplicity p n :=
begin
  obtain hyx | hyx := le_total y x,
 { iterate 2 { rw ← int.coe_nat_multiplicity },
    rw int.coe_nat_sub (nat.pow_le_pow_of_le_left hyx n),
    rw ← int.coe_nat_dvd at hxy hx,
    push_cast at *,
    exact int.pow_sub_pow hp hp1 hxy hx n },
  { simp only [nat.sub_eq_zero_iff_le.mpr hyx,
      nat.sub_eq_zero_iff_le.mpr (nat.pow_le_pow_of_le_left hyx n), multiplicity.zero,
      part_enat.top_add] }
end

lemma nat.pow_add_pow {x y : ℕ} (hxy : p ∣ x + y) (hx : ¬p ∣ x) {n : ℕ} (hn : odd n) :
  multiplicity p (x ^ n + y ^ n) = multiplicity p (x + y) + multiplicity p n :=
begin
  iterate 2 { rw [←int.coe_nat_multiplicity] },
  rw ←int.coe_nat_dvd at hxy hx,
  push_cast at *,
  exact int.pow_add_pow hp hp1 hxy hx hn
end

end lifting_the_exponent
end multiplicity
end comm_ring

lemma pow_two_pow_sub_pow_two_pow [comm_ring R] {x y : R} (n : ℕ) :
  x ^ (2 ^ n) - y ^ (2 ^ n) = (∏ i in finset.range n, (x ^ (2 ^ i) + y ^ (2 ^ i))) * (x - y) :=
begin
  induction n with d hd,
  { simp only [pow_zero, pow_one, finset.range_zero, finset.prod_empty, one_mul] },
  { suffices : x ^ 2 ^ d.succ - y ^ 2 ^ d.succ = (x ^ 2 ^ d + y ^ 2 ^ d) * (x ^ 2 ^ d - y ^ 2 ^ d),
    { rw [this, hd, finset.prod_range_succ, ← mul_assoc, mul_comm (x ^ 2 ^ d + y ^ 2 ^ d)] },
    { ring_exp_eq } }
end

lemma _root_.int.sq_mod_four_eq_one_of_odd {x : ℤ} : odd x → x ^ 2 % 4 = 1 :=
begin
  intro hx,
  -- Replace `x : ℤ` with `y : zmod 4`
  replace hx : x % (2 : ℕ) = 1 % (2 : ℕ), { rw int.odd_iff at hx, norm_num [hx] },
  calc x^2 % (4 : ℕ)
      = 1 % (4 : ℕ) : _
  ... = 1 : by norm_num,
  rw ← zmod.int_coe_eq_int_coe_iff' at hx ⊢,
  push_cast,
  rw [← map_int_cast (zmod.cast_hom (show 2 ∣ 4, by norm_num) (zmod 2)) x] at hx,
  set y : zmod 4 := x,
  change zmod.cast_hom _ (zmod 2) y = _ at hx,
  -- Now we can just consider each of the 4 possible values for y
  fin_cases y using hy;
    rw hy at ⊢ hx; revert hx; dec_trivial
end

lemma int.two_pow_two_pow_add_two_pow_two_pow {x y : ℤ}
  (hx : ¬ 2 ∣ x) (hxy : 4 ∣ (x - y))
  (i : ℕ) : multiplicity 2 (x ^ 2 ^ i + y ^ 2 ^ i) = ↑(1 : ℕ) :=
begin
  have hx_odd : odd x, { rwa [int.odd_iff_not_even, even_iff_two_dvd] },
  have hxy_even : even (x - y) := even_iff_two_dvd.mpr (dvd_trans (by norm_num) hxy),
  have hy_odd : odd y := by simpa using hx_odd.sub_even hxy_even,
  refine multiplicity.eq_coe_iff.mpr ⟨_, _⟩,
  { rw [pow_one, ← even_iff_two_dvd],
    exact (hx_odd.pow).add_odd hy_odd.pow },
  cases i with i,
  { intro hxy',
    have : 2 * 2 ∣ 2 * x, { convert dvd_add hxy hxy', ring_exp },
    have : 2 ∣ x := (mul_dvd_mul_iff_left (by norm_num)).mp this,
    contradiction },
  suffices : ∀ (x : ℤ), odd x → x ^ (2 ^ (i + 1)) % 4 = 1,
  { rw [show (2 ^ (1 + 1) : ℤ) = 4, by norm_num, int.dvd_iff_mod_eq_zero, int.add_mod,
        this _ hx_odd, this _ hy_odd],
    norm_num },
  intros x hx,
  rw [pow_succ, mul_comm, pow_mul, int.sq_mod_four_eq_one_of_odd hx.pow]
end

lemma int.two_pow_two_pow_sub_pow_two_pow {x y : ℤ} (n : ℕ) (hxy : 4 ∣ x - y) (hx : ¬ 2 ∣ x) :
  multiplicity 2 (x ^ (2 ^ n) - y ^ (2 ^ n)) = multiplicity 2 (x - y) + n :=
by simp only [pow_two_pow_sub_pow_two_pow  n, multiplicity.mul int.prime_two,
    multiplicity.finset.prod (int.prime_two), add_comm, nat.cast_one, finset.sum_const,
    finset.card_range, nsmul_one, int.two_pow_two_pow_add_two_pow_two_pow hx hxy]

lemma int.two_pow_sub_pow' {x y : ℤ} (n : ℕ) (hxy : 4 ∣ x - y) (hx : ¬ 2 ∣ x) :
  multiplicity 2 (x ^ n - y ^ n) = multiplicity 2 (x - y) + multiplicity (2 : ℤ) n :=
begin
  have hx_odd : odd x, { rwa [int.odd_iff_not_even, even_iff_two_dvd] },
  have hxy_even : even (x - y) := even_iff_two_dvd.mpr (dvd_trans (by norm_num) hxy),
  have hy_odd : odd y := by simpa using hx_odd.sub_even hxy_even,
  cases n,
  { simp only [pow_zero, sub_self, multiplicity.zero, int.coe_nat_zero, part_enat.add_top] },
  have h : (multiplicity 2 n.succ).dom := multiplicity.finite_nat_iff.mpr ⟨by norm_num, n.succ_pos⟩,
  rcases multiplicity.eq_coe_iff.mp (part_enat.coe_get h).symm with ⟨⟨k, hk⟩, hpn⟩,
  rw [hk, pow_mul, pow_mul, multiplicity.pow_sub_pow_of_prime,
      int.two_pow_two_pow_sub_pow_two_pow _ hxy hx,
      ← hk, part_enat.coe_get],
  { norm_cast },
  { exact int.prime_two },
  { simpa only [even_iff_two_dvd] using hx_odd.pow.sub_odd hy_odd.pow },
  { simpa only [even_iff_two_dvd, int.odd_iff_not_even] using hx_odd.pow },
  erw [int.coe_nat_dvd], -- `erw` to deal with `2 : ℤ` vs `(2 : ℕ) : ℤ`
  contrapose! hpn,
  rw pow_succ',
  conv_rhs { rw hk },
  exact mul_dvd_mul_left _ hpn
end

/-- **Lifting the exponent lemma** for `p = 2` -/
lemma int.two_pow_sub_pow {x y : ℤ} {n : ℕ} (hxy : 2 ∣ x - y) (hx : ¬ 2 ∣ x) (hn : even n) :
  multiplicity 2 (x ^ n - y ^ n) + 1 = multiplicity 2 (x + y) + multiplicity 2 (x - y) +
    multiplicity (2 : ℤ) n :=
begin
  have hy : odd y,
  { rw [← even_iff_two_dvd, ← int.odd_iff_not_even] at hx,
    replace hxy := (@even_neg _ _ (x - y)).mpr (even_iff_two_dvd.mpr hxy),
    convert even.add_odd hxy hx,
    abel },
  cases hn with d hd,
  subst hd,
  simp only [← two_mul, pow_mul],
  have hxy4 : 4 ∣ x ^ 2 - y ^ 2,
  { rw [int.dvd_iff_mod_eq_zero, int.sub_mod, int.sq_mod_four_eq_one_of_odd _,
      int.sq_mod_four_eq_one_of_odd hy],
    { norm_num },
    { simp only [int.odd_iff_not_even, even_iff_two_dvd, hx, not_false_iff] }},
  rw [int.two_pow_sub_pow' d hxy4 _, sq_sub_sq, ← int.coe_nat_mul_out,
    multiplicity.mul (int.prime_two), multiplicity.mul (int.prime_two)],
  suffices : multiplicity (2 : ℤ) ↑(2 : ℕ) = 1,
  { rw [this, add_comm (1 : part_enat), ← add_assoc] },
  { norm_cast,
    rw multiplicity.multiplicity_self _ _,
    { apply prime.not_unit,
      simp only [← nat.prime_iff, nat.prime_two] },
    { exact two_ne_zero }},
  { rw [← even_iff_two_dvd, ← int.odd_iff_not_even],
    apply odd.pow,
    simp only [int.odd_iff_not_even, even_iff_two_dvd, hx, not_false_iff] }
end

lemma nat.two_pow_sub_pow {x y : ℕ} (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) {n : ℕ} (hn : even n) :
  multiplicity 2 (x ^ n - y ^ n) + 1 = multiplicity 2 (x + y) + multiplicity 2 (x - y) +
    multiplicity 2 n :=
begin
  obtain hyx | hyx := le_total y x,
  { iterate 3 { rw ←multiplicity.int.coe_nat_multiplicity },
    have hxyn : y ^ n ≤ x ^ n := pow_le_pow_of_le_left' hyx _,
    simp only [int.coe_nat_sub hyx, int.coe_nat_sub (pow_le_pow_of_le_left' hyx _), int.coe_nat_add,
      int.coe_nat_pow],
    rw ←int.coe_nat_dvd at hx,
    rw [←int.coe_nat_dvd, int.coe_nat_sub hyx] at hxy,
    convert int.two_pow_sub_pow hxy hx hn using 2,
    rw ← multiplicity.int.coe_nat_multiplicity,
    refl },
  { simp only [nat.sub_eq_zero_iff_le.mpr hyx,
      nat.sub_eq_zero_iff_le.mpr (pow_le_pow_of_le_left' hyx n), multiplicity.zero,
      part_enat.top_add, part_enat.add_top] }
end

namespace padic_val_nat

variables {x y : ℕ}

lemma pow_two_sub_pow (hyx : y < x) (hxy : 2 ∣ x - y) (hx : ¬ 2 ∣ x) {n : ℕ} (hn : 0 < n)
  (hneven : even n) :
  padic_val_nat 2 (x ^ n - y ^ n) + 1 =
    padic_val_nat 2 (x + y) + padic_val_nat 2 (x - y) + padic_val_nat 2 n :=
begin
  simp only [←part_enat.coe_inj, nat.cast_add],
  iterate 4 { rw [padic_val_nat_def, part_enat.coe_get] },
  { convert nat.two_pow_sub_pow hxy hx hneven using 2 },
  { exact hn },
  { exact (nat.sub_pos_of_lt hyx) },
  { linarith },
  { simp only [tsub_pos_iff_lt, pow_lt_pow_of_lt_left hyx (@zero_le' _ y _) hn] }
end

variables {p : ℕ} [hp : fact p.prime] (hp1 : odd p)
include hp hp1

lemma pow_sub_pow (hyx : y < x) (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : ℕ} (hn : 0 < n) :
  padic_val_nat p (x ^ n - y ^ n) = padic_val_nat p (x - y) + padic_val_nat p n :=
begin
  rw [←part_enat.coe_inj, nat.cast_add],
  iterate 3 { rw [padic_val_nat_def, part_enat.coe_get] },
  { exact multiplicity.nat.pow_sub_pow hp.out hp1 hxy hx n },
  { exact hn },
  { exact nat.sub_pos_of_lt hyx },
  { exact nat.sub_pos_of_lt (nat.pow_lt_pow_of_lt_left hyx hn) }
end

lemma pow_add_pow (hxy : p ∣ x + y) (hx : ¬p ∣ x) {n : ℕ} (hn : odd n) :
  padic_val_nat p (x ^ n + y ^ n) = padic_val_nat p (x + y) + padic_val_nat p n :=
begin
  cases y,
  { have := dvd_zero p, contradiction },
  rw [←part_enat.coe_inj, nat.cast_add],
  iterate 3 { rw [padic_val_nat_def, part_enat.coe_get] },
  { exact multiplicity.nat.pow_add_pow hp.out hp1 hxy hx hn },
  { exact (odd.pos hn) },
  { simp only [add_pos_iff, nat.succ_pos', or_true] },
  { exact (nat.lt_add_left _ _ _ (pow_pos y.succ_pos _)) }
end

end padic_val_nat
