/-
Copyright (c) 2022 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/
import algebra.geom_sum
import data.nat.parity
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

variables {α R : Type*}

open ideal ideal.quotient

section ring
variables [ring α]

lemma dvd_sub_comm {a b c : α} : a ∣ b - c ↔ a ∣ c - b := by rw [←dvd_neg, neg_sub]

end ring

section comm_ring
variables [comm_ring R]

lemma dvd_geom_sum₂ {n : ℕ} {x y : R} (h : ↑n ∣ x - y) : ↑n ∣ geom_sum₂ x y n :=
begin
  rw ←mem_span_singleton at ⊢ h,
  rw ←ideal.quotient.eq at h,
  rw [←eq_zero_iff_mem, ring_hom.map_geom_sum₂, h, geom_sum₂_self],
  apply mul_eq_zero_of_left,
  rw [←map_nat_cast (mk $ span ({n} : set R)) n, eq_zero_iff_mem, mem_span_singleton],
end

lemma multiplicity.geom_sum₂_eq_zero [@decidable_rel R (∣)] {p : R} (hp : prime p)
  {x y : R} (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : ℕ} (hn : ¬p ∣ n) :
  multiplicity p (geom_sum₂ x y n) = 0 :=
begin
  apply multiplicity.multiplicity_eq_zero_of_not_dvd,
  rw ←mem_span_singleton at *,
  rw ←ideal.quotient.eq at hxy,
  rw ←eq_zero_iff_mem at *,
  haveI := (span_singleton_prime hp.1).mpr hp,
  rw [ring_hom.map_geom_sum₂, ←hxy, geom_sum₂_self, mul_eq_zero],
  exact not_or (by rwa map_nat_cast at hn) (λ h, hx $ pow_eq_zero h),
end

section helpers

open_locale big_operators

variables {a b : R} {p n : ℕ} (hp2 : (p : R) ^ 2 = 0)
include hp2

private lemma add_mul_pow_eq : (a + p * b) ^ n = a ^ (n - 1) * (p * b) * n + a ^ n :=
begin
  cases n,
  { rw [pow_zero, pow_zero, nat.cast_zero, mul_zero, zero_add] },
  suffices : ∀ i ∈ finset.range n, a ^ i * (p * b) ^ (n + 1 - i) * (n + 1).choose i = 0,
  { rw [nat.succ_sub_one, ←nat.add_one, add_pow, finset.sum_range_succ, finset.sum_range_succ,
      finset.sum_eq_zero this, nat.choose_self, nat.cast_one, nat.choose_succ_self_right,
      nat.sub_self, nat.add_sub_cancel_left],
    ring },
  intros i hi,
  have h : (0 : R) ∣ p ^ (n + 1 - i) := hp2 ▸ pow_dvd_pow _
    (le_tsub_of_add_le_left $ nat.succ_le_succ $ finset.mem_range.mp hi),
  rw [mul_pow, eq_zero_of_zero_dvd h, zero_mul, mul_zero, zero_mul],
end

alias even_iff_two_dvd ↔ even.two_dvd _

private lemma geom_sum₂_add_mul (hp : odd p) : geom_sum₂ (a + p * b) a p = p * a ^ (p - 1) :=
have h : ∀ i ∈ finset.range p, a ^ ((i - 1) + (p - 1 - i)) * i = a ^ (p - 2) * i,
begin
  intros i hi,
  cases i,
  { rw [nat.cast_zero, mul_zero, mul_zero] },
  { congr' 2,
    rw ←nat.add_sub_assoc (nat.le_pred_of_lt (finset.mem_range.mp hi)),
    exact congr_arg nat.pred (nat.add_sub_cancel_left _ _) }
end,
calc  ∑ i in finset.range p, (a + p * b) ^ i * a ^ (p - 1 - i)
    = ∑ i in finset.range p,
        (a ^ i * a ^ (p - 1 - i) + b * p * (a ^ ((i - 1) + (p - 1 - i)) * i)) :
  finset.sum_congr rfl $ λ i hi, by rw add_mul_pow_eq hp2; ring_exp
... = p * a ^ (p - 1) + b * a ^ (p - 2) * ↑((p - 1) / 2) * ↑p ^ 2 :
  by rw [finset.sum_add_distrib, ←geom_sum₂, geom_sum₂_self, ←finset.mul_sum,
    finset.sum_congr rfl h, ←finset.mul_sum, ←nat.cast_sum, finset.sum_range_id,
    nat.mul_div_assoc _ (hp.sub_odd odd_one).two_dvd, nat.cast_mul]; ring
... = p * a ^ (p - 1) :
  by rw [hp2, mul_zero, add_zero]

end helpers

end comm_ring

namespace multiplicity

section integral_domain
variables [comm_ring R] [is_domain R] [@decidable_rel R (∣)]

lemma pow_sub_pow' {p : R} (hp : prime p) {x y : R} (hxy : p ∣ x - y) (hx : ¬p ∣ x)
  {n : ℕ} (hn : ¬p ∣ n) :
  multiplicity p (x ^ n - y ^ n) = multiplicity p (x - y) :=
by rw [←geom_sum₂_mul, multiplicity.mul hp, geom_sum₂_eq_zero hp hxy hx hn, zero_add]

variables {p : ℕ} (hp : prime (p : R)) (hp1 : odd p) {x y : R} (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x)
include hp hp1 hxy hx

lemma geom_sum₂_eq_one : multiplicity ↑p (geom_sum₂ x y p) = 1 :=
begin
  rw ←nat.cast_one,
  refine multiplicity.eq_coe_iff.2 ⟨_, _⟩,
  { rw pow_one,
    exact dvd_geom_sum₂ hxy },
  let I : ideal R := span {p ^ 2},
  have hp' : (p : R ⧸ I) ^ 2 = 0,
  { rw [←map_nat_cast (mk I), ←ring_hom.map_pow, eq_zero_iff_mem, mem_span_singleton] },
  rw dvd_iff_dvd_of_dvd_sub hxy at hx,
  cases hxy with k hk,
  rw [←mem_span_singleton, ←eq_zero_iff_mem, ring_hom.map_geom_sum₂, sub_eq_iff_eq_add'.mp hk,
    ring_hom.map_add, ring_hom.map_mul, map_nat_cast, geom_sum₂_add_mul hp' hp1,
    ←map_nat_cast (mk I), ←ring_hom.map_pow, ←ring_hom.map_mul, eq_zero_iff_mem,
    mem_span_singleton, pow_two, mul_dvd_mul_iff_left hp.1],
  exact λ h, hx (hp.dvd_of_dvd_pow h)
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
variables {p : ℕ} (hp : p.prime) (hp1 : odd p)
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

lemma nat.pow_sub_pow {x y : ℕ} (hyx : y ≤ x) (hxy : p ∣ x - y) (hx : ¬p ∣ x) (n : ℕ) :
  multiplicity p (x ^ n - y ^ n) = multiplicity p (x - y) + multiplicity p n :=
begin
  iterate 2 { rw ←int.coe_nat_multiplicity },
  rw [int.coe_nat_sub (nat.pow_le_pow_of_le_left hyx n),
    int.coe_nat_pow, int.coe_nat_pow],
  rw ←int.coe_nat_dvd at hxy hx,
  rw int.coe_nat_sub hyx at hxy ⊢,
  exact int.pow_sub_pow hp hp1 hxy hx n,
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

namespace padic_val_nat
section

variables {p : ℕ} [hp : fact p.prime] (hp1 : odd p) {x y : ℕ}
include hp hp1

lemma pow_sub_pow (hyx : y < x) (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : ℕ} (hn : 0 < n) :
  padic_val_nat p (x ^ n - y ^ n) = padic_val_nat p (x - y) + padic_val_nat p n :=
begin
  rw [←enat.coe_inj, nat.cast_add],
  iterate 3 { rw [padic_val_nat_def, enat.coe_get] },
  { exact multiplicity.nat.pow_sub_pow hp.out hp1 hyx.le hxy hx n },
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

end
end padic_val_nat
