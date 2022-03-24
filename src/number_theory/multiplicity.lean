/-
Copyright (c) 2022 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/
import algebra.geom_sum
import data.int.parity
import number_theory.padics.padic_norm

/-!
# Multiplicity in Number Theory

This file contains results in number theory relating to multiplicity.

## Main statements

* `multiplicity.int.pow_sub_pow` is the lifting the exponent lemma for odd primes.
  We also prove several variations of the lemma.

## References

* [Wikipedia, *Lifting-the-exponent lemma*]
  (https://en.wikipedia.org/wiki/Lifting-the-exponent_lemma)
-/

open ideal ideal.quotient
open_locale big_operators

variables {R : Type*} {n : ℕ}


section comm_ring
variables [comm_ring R] {a b x y : R}


lemma dvd_geom_sum₂ {x y : R} (h : ↑n ∣ x - y) : ↑n ∣ geom_sum₂ x y n :=
begin
  rw ← mem_span_singleton at ⊢ h,
  rw ← ideal.quotient.eq at h,
  rw [← eq_zero_iff_mem, ring_hom.map_geom_sum₂, h, geom_sum₂_self],
  apply mul_eq_zero_of_left,
  rw [← map_nat_cast (mk $ span ({n} : set R)) n, eq_zero_iff_mem, mem_span_singleton]
end

lemma sq_dvd_add_mul_pow_sub (p x y : R) (n : ℕ) :
  p ^ 2 ∣ (x + p * y) ^ n - (x ^ (n - 1) * (p * y) * n + x ^ n) :=
begin
  cases n,
  { simp only [pow_zero, nat.cast_zero, mul_zero, sub_self, dvd_zero, zero_add] },
  { simp only [nat.succ_sub_succ_eq_sub, tsub_zero, nat.cast_succ, add_pow,
    finset.sum_range_succ, nat.choose_self, nat.succ_sub _, tsub_self, pow_one,
    nat.choose_succ_self_right, pow_zero, mul_one, nat.cast_zero, zero_add, nat.succ_eq_add_one],
    abel,
    apply finset.dvd_sum,
    intros x hx,
    apply dvd_mul_of_dvd_left,
    apply dvd_mul_of_dvd_right,
    rw mul_pow,
    apply dvd_mul_of_dvd_left,
    apply pow_dvd_pow,
    apply le_tsub_of_add_le_left,
    linarith [finset.mem_range.mp hx]  },
end

lemma not_dvd_geom_sum₂ {p : R} (hp : prime p)
  (hxy : p ∣ x - y) (hx : ¬p ∣ x) (hn : ¬p ∣ n) :
  ¬p ∣ geom_sum₂ x y n :=
begin
  rw ← mem_span_singleton at *,
  rw ← ideal.quotient.eq at hxy,
  rw ← eq_zero_iff_mem at *,
  haveI := (span_singleton_prime hp.1).mpr hp,
  rw [ring_hom.map_geom_sum₂, ←hxy, geom_sum₂_self, mul_eq_zero],
  exact not_or (by rwa map_nat_cast at hn) (λ h, hx $ pow_eq_zero h)
end

variables {p : ℕ}

lemma odd_sq_dvd_geom_sum₂_sub (hp : odd p) :
  ↑p ^ 2 ∣ geom_sum₂ (a + p * b) a p - p * a ^ (p - 1) :=
begin
  have h1 := λ i, sq_dvd_add_mul_pow_sub ↑p a b i,
  simp_rw [← mem_span_singleton, ← ideal.quotient.eq] at *,
  simp_rw [ring_hom.map_geom_sum₂, geom_sum₂, ← map_pow, h1, ← ring_hom.map_mul],
  ring_exp,
  simp only [← pow_add, ring_hom.map_add, finset.sum_add_distrib, ← ring_hom.map_sum],
  have h2 : (∑ (x : ℕ) in finset.range p, a ^ (x + (p - 1 - x))) =
    ∑ (x : ℕ) in finset.range p, a ^ (p - 1),
  { apply finset.sum_congr rfl,
    intros x hx,
    congr,
    rw finset.mem_range at hx,
    have hxp : x ≤ p - 1, { exact nat.le_pred_of_lt hx },
    zify [hxp],
    simp only [add_sub_cancel'_right] },
  simp only [finset.sum_const, finset.card_range, nsmul_eq_mul] at h2,
  simp only [h2, add_left_eq_self, ← mul_assoc, ← pow_add, mul_comm b _, mul_comm ↑p _,
    ← finset.sum_mul],
  have h3 : ∑ (x : ℕ) in finset.range p, a ^ (x - 1 + (p - 1 - x)) * ↑x =
    ∑ (x : ℕ) in finset.range p, a ^ (p - 2) * x,
  { apply finset.sum_congr rfl _,
    intros i hi,
    cases i,
    { rw [nat.cast_zero, mul_zero, mul_zero] },
    { congr' 2,
      rw ←nat.add_sub_assoc (nat.le_pred_of_lt (finset.mem_range.mp hi)),
      exact congr_arg nat.pred (nat.add_sub_cancel_left _ _) }},
  rw [h3, ← finset.mul_sum, ← nat.cast_sum, finset.sum_range_id,
    nat.mul_div_assoc _ (even_iff_two_dvd.mp (nat.odd.sub_odd hp odd_one)), nat.cast_mul],
  ring_exp,
  simp only [ring_hom.map_mul, mul_eq_zero_of_right, mul_eq_zero_of_left,
    ideal.quotient.eq_zero_iff_mem, mem_span_singleton],
end


namespace multiplicity

section integral_domain
variables [is_domain R] [@decidable_rel R (∣)]

lemma pow_sub_pow' {p : R} (hp : prime p) {x y : R} (hxy : p ∣ x - y) (hx : ¬p ∣ x)
  {n : ℕ} (hn : ¬p ∣ n) :
  multiplicity p (x ^ n - y ^ n) = multiplicity p (x - y) :=
by rw [←geom_sum₂_mul, multiplicity.mul hp,
  multiplicity_eq_zero_of_not_dvd (not_dvd_geom_sum₂ hp hxy hx hn), zero_add]

variables (hp : prime (p : R)) (hp1 : odd p) (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x)
include hp hp1 hxy hx

lemma geom_sum₂_eq_one : multiplicity ↑p (geom_sum₂ x y p) = 1 :=
begin
  rw ← nat.cast_one,
  refine multiplicity.eq_coe_iff.2 ⟨_, _⟩,
  { rw pow_one,
    exact dvd_geom_sum₂ hxy },
  { have hy : ¬↑p ∣ y,
    { intro y,
      apply hx,
      exact (dvd_iff_dvd_of_dvd_sub hxy).mpr y },
    cases hxy with k hk,
    replace hk : x = y + p * k, { exact eq_add_of_sub_eq' hk },
    have h1 := @odd_sq_dvd_geom_sum₂_sub _ _ y k _ hp1,
    intro hp1,
    rw [one_add_one_eq_two, hk] at hp1,
    replace h1 : ↑p ^ 2 ∣ ↑p * y ^ (p - 1), { exact (dvd_iff_dvd_of_dvd_sub h1).mp hp1 },
    rw [pow_two, mul_dvd_mul_iff_left] at h1,
    { replace h1 := prime.dvd_of_dvd_pow hp h1,
      exact hy h1 },
    { exact prime.ne_zero hp } }
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
  rcases eq_coe_iff.mp (enat.coe_get h).symm with ⟨⟨k, hk⟩, hpn⟩,
  conv_lhs { rw [hk, pow_mul, pow_mul] },
  rw nat.prime_iff_prime_int at hp,
  rw ←int.nat_cast_eq_coe_nat at *,
  rw [pow_sub_pow' hp, pow_prime_pow_sub_pow_prime_pow hp hp1 hxy hx, enat.coe_get],
  { rw ←geom_sum₂_mul,
    exact dvd_mul_of_dvd_right hxy _ },
  { exact λ h, hx (hp.dvd_of_dvd_pow h) },
  { iterate 2 { rw int.nat_cast_eq_coe_nat },
    rw int.coe_nat_dvd,
    rintro ⟨c, rfl⟩,
    refine hpn ⟨c, _⟩,
    rwa [pow_succ', mul_assoc] }
end


lemma int.pow_add_pow {x y : ℤ} (hxy : ↑p ∣ x + y) (hx : ¬↑p ∣ x) {n : ℕ} (hn : odd n) :
  multiplicity ↑p (x ^ n + y ^ n) = multiplicity ↑p (x + y) + multiplicity p n :=
begin
  rw ←sub_neg_eq_add at hxy,
  rw [←sub_neg_eq_add, ←sub_neg_eq_add, ←nat.odd.neg_pow hn],
  exact int.pow_sub_pow hp hp1 hxy hx n,
end

lemma nat.pow_sub_pow {x y : ℕ} (hxy : p ∣ x - y) (hx : ¬p ∣ x) (n : ℕ) :
  multiplicity p (x ^ n - y ^ n) = multiplicity p (x - y) + multiplicity p n :=
begin
  obtain hyx | hyx := le_total y x,
  { iterate 2 { rw ←int.coe_nat_multiplicity },
    rw [int.coe_nat_sub (nat.pow_le_pow_of_le_left hyx n),
    int.coe_nat_pow, int.coe_nat_pow],
    rw ←int.coe_nat_dvd at hxy hx,
    rw int.coe_nat_sub hyx at hxy ⊢,
    exact int.pow_sub_pow hp hp1 hxy hx n },
  { simp only [nat.sub_eq_zero_iff_le.mpr hyx,
      nat.sub_eq_zero_iff_le.mpr (nat.pow_le_pow_of_le_left hyx n), multiplicity.zero,
        enat.top_add] },
end

lemma nat.pow_add_pow {x y : ℕ} (hxy : p ∣ x + y) (hx : ¬p ∣ x) {n : ℕ} (hn : odd n) :
  multiplicity p (x ^ n + y ^ n) = multiplicity p (x + y) + multiplicity p n :=
begin
  iterate 2 { rw [←int.coe_nat_multiplicity, int.coe_nat_add, int.coe_nat_pow] },
  rw ←int.coe_nat_dvd at hxy hx,
  rw int.coe_nat_add at hxy,
  exact int.pow_add_pow hp hp1 hxy hx hn,
end

end lifting_the_exponent
end multiplicity
end comm_ring

namespace multiplicity

lemma int.pow_two_sub_pow_two_eq_factorisation {x y : ℤ} (n : ℕ) :
  x ^ (2 ^ n) - y ^ (2 ^ n) = (∏ i in finset.range n, (x ^ (2 ^ i) + y ^ (2 ^ i))) * (x - y) :=
begin
  induction n with d hd,
  { simp only [pow_zero, pow_one, finset.range_zero, finset.prod_empty, one_mul] },
  { suffices : x ^ 2 ^ d.succ - y ^ 2 ^ d.succ = (x ^ 2 ^ d + y ^ 2 ^ d) * (x ^ 2 ^ d - y ^ 2 ^ d),
    { rw [this, hd, finset.prod_range_succ, ← mul_assoc, mul_comm (x ^ 2 ^ d + y ^ 2 ^ d)] },
    { ring_exp_eq }}
end

lemma int.sq_mod_four_eq_one_of_odd {x : ℤ} : odd x → x ^ 2 % 4 = 1 :=
begin
  intro hx,
  rw int.odd_iff at hx,
  suffices : x ^ 2 % 4 = 1 % 4,
  { norm_num [this] },
  { rw int.mod_eq_mod_iff_mod_sub_eq_zero,
    suffices : (x ^ 2 - 1 ^ 2) % 4 = 0,
    { convert this },
    { rw sq_sub_sq,
      apply int.mod_eq_zero_of_dvd,
      suffices : 2 * 2 ∣ (x + 1) * (x - 1),
      { convert this },
      apply mul_dvd_mul,
      { rw [int.dvd_iff_mod_eq_zero, int.add_mod, hx],
        norm_num },
      { rw [int.dvd_iff_mod_eq_zero, int.sub_mod, hx],
        norm_num }}}
end

lemma int.two_pow_two_sub_pow {x y : ℤ} (n : ℕ) (hxy : 4 ∣ x - y) (hx : ¬ 2 ∣ x) :
  multiplicity 2 (x ^ (2 ^ n) - y ^ (2 ^ n)) = multiplicity 2 (x - y) + n :=
begin
  simp only [int.pow_two_sub_pow_two_eq_factorisation n, multiplicity.mul (int.prime_two),
    multiplicity.finset.prod (int.prime_two)],
  have hyodd : odd y,
  { have hsub : even (y - x),
        { rw [even_iff_two_dvd, ← dvd_neg, neg_sub],
          apply dvd_trans (show (2 : ℤ) ∣ 4, by norm_num) hxy },
        rw [← sub_add_cancel y x],
        apply even.add_odd hsub,
        simp only [int.odd_iff_not_even, even_iff_two_dvd, hx, not_false_iff] },
  have hi : ∀ (i : ℕ), multiplicity 2 (x ^ 2 ^ i + y ^ 2 ^ i) = ↑(1 : ℕ),
  { intro i,
    rw multiplicity.eq_coe_iff,
    split,
    { rw [pow_one, ← even_iff_two_dvd],
      apply odd.add_odd,
      { apply odd.pow,
        simp only [int.odd_iff_not_even, even_iff_two_dvd, hx, not_false_iff] },
      { apply odd.pow hyodd }},
    norm_num,
    rw int.dvd_iff_mod_eq_zero,
    obtain rfl | hnezero := eq_or_ne i 0,
    { simp only [pow_zero, pow_one, euclidean_domain.mod_eq_zero],
      suffices : ¬ 2 * 2 ∣ x + y,
      { convert this },
      { intro hyx,
        replace hyx := dvd_add hyx hxy,
        simp only [←two_mul, mul_one, add_add_sub_cancel, pow_two] at hyx,
        rw mul_dvd_mul_iff_left (show (2 : ℤ) ≠ 0, by norm_num) at hyx,
          exact hx hyx }},
      have hixy : x ^ 2 ^ i % 4 = 1 ∧ y ^ 2 ^ i % 4 = 1,
      { suffices : (x ^ 2 ^ (i - 1)) ^ 2 % 4 = 1 ∧ (y ^ 2 ^ (i-1)) ^ 2 % 4 = 1,
        { convert this using 3;
          { rw [← pow_mul, ← pow_succ', nat.sub_add_cancel (nat.one_le_iff_ne_zero.mpr hnezero)] }},
          split,
          { apply int.sq_mod_four_eq_one_of_odd,
            apply odd.pow,
            simp only [int.odd_iff_not_even, even_iff_two_dvd, hx, not_false_iff] },
          { apply int.sq_mod_four_eq_one_of_odd,
            apply odd.pow hyodd }},
    rw [int.add_mod, hixy.1, hixy.2],
    norm_num },
  { simp only [hi, add_comm, nat.cast_one, finset.sum_const, finset.card_range, nsmul_one] }
end

lemma int.two_pow_sub_pow' {x y : ℤ} (n : ℕ) (hxy : 4 ∣ x - y) (hx : ¬ 2 ∣ x) :
  multiplicity 2 (x ^ n - y ^ n) = multiplicity 2 (x - y) + multiplicity (2 : ℤ) n :=
begin
  have hy : ¬ 2 ∣ y,
  { rw [← even_iff_two_dvd, ← int.odd_iff_not_even] at *,
    replace hxy := (even_neg (x - y)).mpr (even_iff_two_dvd.mpr
      (dvd_trans (show (2 : ℤ) ∣ 4, by norm_num) hxy)),
    convert even.add_odd hxy hx,
    abel },
  cases n,
  { simp only [pow_zero, sub_self, multiplicity.zero, int.coe_nat_zero, enat.add_top] },
  { have h : (multiplicity 2 n.succ).dom := finite_nat_iff.mpr
    ⟨nat.bit0_ne_one 1, n.succ_pos⟩,
  rcases eq_coe_iff.mp (enat.coe_get h).symm with ⟨⟨k, hk⟩, hpn⟩,
  rw hk,
  have hxpow : ¬ 2 ∣ x ^ 2 ^ (multiplicity 2 n.succ).get h,
  { rw [← even_iff_two_dvd, ← int.odd_iff_not_even],
    apply odd.pow,
    simp only [int.odd_iff_not_even, even_iff_two_dvd, hx, not_false_iff] },
  have hxy2 : 2 ∣ x ^ 2 ^ (multiplicity 2 n.succ).get h - y ^ 2 ^ (multiplicity 2 n.succ).get h,
  { rw [← even_iff_two_dvd],
    apply odd.sub_odd,
    { apply odd.pow,
      simp only [int.odd_iff_not_even, even_iff_two_dvd, hx, not_false_iff] },
    { apply odd.pow,
      simp only [int.odd_iff_not_even, even_iff_two_dvd, hy, not_false_iff] }},
  have hk2 : ¬ (2 : ℤ) ∣ k,
  { norm_cast,
    contrapose hpn,
    simp only [not_not, pow_add, pow_one],
    suffices : 2 ^ (multiplicity 2 n.succ).get h * 2 ∣ 2 ^ (multiplicity 2 n.succ).get h * k,
    { convert this },
    apply mul_dvd_mul,
    { exact dvd_rfl },
    { exact (not_not.mp hpn) }},
  simp only [pow_mul],
  rw pow_sub_pow'(int.prime_two) hxy2 hxpow _,
  { simp only [int.two_pow_two_sub_pow ((multiplicity 2 n.succ).get h) hxy hx],
    rw [← hk],
    simp only [enat.coe_get, int.coe_nat_succ, ← int.coe_nat_multiplicity],
    refl  },
  simp only [hk2, int.nat_cast_eq_coe_nat, not_false_iff] }
end

/-- **Lifting the exponent lemma** for `p = 2` -/
lemma int.two_pow_sub_pow {x y : ℤ} {n : ℕ} (hxy : 2 ∣ x - y) (hx : ¬ 2 ∣ x) (hn : even n) :
  multiplicity 2 (x ^ n  - y ^ n) + 1 = multiplicity 2 (x + y) + multiplicity 2 (x - y) +
    multiplicity (2 : ℤ) n :=
begin
  have hy : odd y,
  { rw [← even_iff_two_dvd, ← int.odd_iff_not_even] at hx,
    replace hxy := (even_neg (x - y)).mpr (even_iff_two_dvd.mpr hxy),
    convert even.add_odd hxy hx,
    abel },
  cases hn with d hd,
  subst hd,
  simp only [pow_mul],
  have hxy4 : 4 ∣ x ^ 2 - y ^ 2,
  { rw [int.dvd_iff_mod_eq_zero, int.sub_mod, int.sq_mod_four_eq_one_of_odd _,
      int.sq_mod_four_eq_one_of_odd hy],
    { norm_num },
    { simp only [int.odd_iff_not_even, even_iff_two_dvd, hx, not_false_iff] }},
  rw [int.two_pow_sub_pow' d hxy4 _, sq_sub_sq, ← int.coe_nat_mul_out,
    multiplicity.mul (int.prime_two), multiplicity.mul (int.prime_two)],
  suffices : multiplicity (2 : ℤ) ↑(2 : ℕ) = 1,
  { rw [this, add_comm (1 : enat), ← add_assoc] },
  { norm_cast,
    rw multiplicity_self _ _,
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
  { iterate 3 { rw ←int.coe_nat_multiplicity },
    have hxyn : y ^ n ≤ x ^ n := pow_le_pow_of_le hyx,
    simp only [int.coe_nat_sub hyx, int.coe_nat_sub (pow_le_pow_of_le hyx), int.coe_nat_add,
      int.coe_nat_pow],
    rw ←int.coe_nat_dvd at hx,
    rw [←int.coe_nat_dvd, int.coe_nat_sub hyx] at hxy,
    convert int.two_pow_sub_pow hxy hx hn using 2,
    rw ← int.coe_nat_multiplicity,
    refl },
  { simp only [nat.sub_eq_zero_iff_le.mpr hyx,
      nat.sub_eq_zero_iff_le.mpr (nat.pow_le_pow_of_le_left hyx n), multiplicity.zero, enat.top_add,
      enat.add_top] }
end

end multiplicity

namespace padic_val_nat

variables {x y : ℕ}

lemma pow_two_sub_pow (hyx : y < x) (hxy : 2 ∣ x - y) (hx : ¬ 2 ∣ x) {n : ℕ} (hn : 0 < n)
  (hneven : even n) : padic_val_nat 2 (x ^ n - y ^ n) + 1 =
    padic_val_nat 2 (x + y) + padic_val_nat 2 (x - y) + padic_val_nat 2 n :=
begin
  simp only [←enat.coe_inj, nat.cast_add],
  iterate 4 { rw [padic_val_nat_def, enat.coe_get] },
  { convert multiplicity.nat.two_pow_sub_pow hxy hx hneven using 2,
    norm_cast },
  { exact ne_of_gt hn },
  { exact ne_of_gt (nat.sub_pos_of_lt hyx) },
  { linarith },
  { simp only [ne.def, tsub_eq_zero_iff_le, not_le, nat.pow_lt_pow_of_lt_left hyx hn] }
end

variables {p : ℕ} [hp : fact p.prime] (hp1 : odd p)
include hp hp1

lemma pow_sub_pow (hyx : y < x) (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : ℕ} (hn : 0 < n) :
  padic_val_nat p (x ^ n - y ^ n) = padic_val_nat p (x - y) + padic_val_nat p n :=
begin
  rw [←enat.coe_inj, nat.cast_add],
  iterate 3 { rw [padic_val_nat_def, enat.coe_get] },
  { exact multiplicity.nat.pow_sub_pow hp.out hp1 hxy hx n },
  all_goals { apply ne_of_gt },
  { exact hn },
  { exact nat.sub_pos_of_lt hyx },
  { exact nat.sub_pos_of_lt (nat.pow_lt_pow_of_lt_left hyx hn) }
end

lemma pow_add_pow (hxy : p ∣ x + y) (hx : ¬p ∣ x) {n : ℕ} (hn : odd n) :
  padic_val_nat p (x ^ n + y ^ n) = padic_val_nat p (x + y) + padic_val_nat p n :=
begin
  cases y,
  { have := dvd_zero p, contradiction },
  rw [←enat.coe_inj, nat.cast_add],
  iterate 3 { rw [padic_val_nat_def, enat.coe_get] },
  { exact multiplicity.nat.pow_add_pow hp.out hp1 hxy hx hn },
  { exact ne_of_gt (nat.odd_gt_zero hn) },
  { exact nat.succ_ne_zero _ },
  { exact (nat.lt_add_left _ _ _ (pow_pos y.succ_pos _)).ne' }
end

end padic_val_nat
