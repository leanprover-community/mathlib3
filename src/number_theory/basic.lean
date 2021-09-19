/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau, Tian Chen
-/

import data.nat.parity
import number_theory.padics.padic_norm

/-!
# Basic results in number theory

This file should contain basic results in number theory.
It contains the essential lemma in the construction of the ring of Witt vectors
and the lifting the exponent lemma.

## Main statements

* `dvd_sub_pow_of_dvd_sub` proves that for elements `a` and `b` in a commutative ring `R` and for
  all natural numbers `p` and `k` if `p` divides `a-b` in `R`, then `p ^ (k + 1)` divides
  `a ^ (p ^ k) - b ^ (p ^ k)`.
* `multiplicity.int.pow_sub_pow` is the lifting the exponent lemma for odd primes.
  We also prove several variations of the lemma.

## References

* <https://en.wikipedia.org/wiki/Lifting-the-exponent_lemma>
-/

section comm_ring

open ideal ideal.quotient

variables {R : Type*} [comm_ring R]

lemma dvd_sub_pow_of_dvd_sub {p : ℕ}
  {a b : R} (h : (p : R) ∣ a - b) (k : ℕ) :
  (p^(k+1) : R) ∣ a^(p^k) - b^(p^k) :=
begin
  induction k with k ih,
  { rwa [pow_one, pow_zero, pow_one, pow_one] },
  rw [pow_succ' p k, pow_mul, pow_mul, ← geom_sum₂_mul, pow_succ],
  refine mul_dvd_mul _ ih,
  let I : ideal R := span {p},
  let f : R →+* ideal.quotient I := mk I,
  have hp : (p : ideal.quotient I) = 0,
  { rw [← f.map_nat_cast, eq_zero_iff_mem, mem_span_singleton] },
  rw [← mem_span_singleton, ← ideal.quotient.eq] at h,
  rw [← mem_span_singleton, ← eq_zero_iff_mem, ring_hom.map_geom_sum₂,
      ring_hom.map_pow, ring_hom.map_pow, h, geom_sum₂_self, hp, zero_mul],
end

lemma multiplicity.geom_sum₂_eq_zero [@decidable_rel R (∣)]
  {p : R} (hp : prime p)
  {x y : R} (hxy₁ : p ∣ x - y) (hxy₂ : ¬p ∣ x * y)
  {n : ℕ} (hn : ¬p ∣ n) :
  multiplicity p (geom_sum₂ x y n) = 0 :=
begin
  apply multiplicity.multiplicity_eq_zero_of_not_dvd,
  rw ← mem_span_singleton at *,
  rw ← ideal.quotient.eq at hxy₁,
  rw ← eq_zero_iff_mem at *,
  haveI := (ideal.span_singleton_prime hp.1).mpr hp,
  rw [ring_hom.map_geom_sum₂, hxy₁, geom_sum₂_self, mul_eq_zero],
  apply not_or,
  { rwa ring_hom.map_nat_cast at hn },
  { rw [ring_hom.map_mul, mul_eq_zero] at hxy₂,
    intro h,
    exact hxy₂ (or.inr (pow_eq_zero h)) }
end

section helpers

open_locale big_operators

variables {a b : R} {p n : ℕ} (hp2 : (p : R) ^ 2 = 0)
include hp2

private lemma add_mul_pow_eq :
  (a + p * b) ^ n = a ^ n + a ^ (n - 1) * (p * b) * n :=
begin
  cases n,
  { rw [pow_zero, pow_zero, nat.cast_zero, mul_zero, add_zero] },
  rw [nat.succ_sub_one, add_pow],
  iterate 2 { rw [finset.range_succ, finset.sum_insert finset.not_mem_range_self] },
  rw [nat.sub_self, pow_zero, nat.choose_self, mul_one, nat.cast_one, mul_one,
    ← nat.add_one, nat.add_sub_cancel_left, pow_one,
    nat.choose_succ_self_right, ← add_assoc, add_right_eq_self],
  apply finset.sum_eq_zero,
  intros i hi,
  have h : (0 : R) ∣ p ^ (n + 1 - i) := hp2 ▸ pow_dvd_pow _
    (nat.le_sub_left_of_add_le $ nat.succ_le_succ $ finset.mem_range.mp hi),
  rw [mul_pow, eq_zero_of_zero_dvd h, zero_mul, mul_zero, zero_mul]
end

private lemma geom_sum₂_add_mul (hp : p % 2 = 1) :
  geom_sum₂ (a + p * b) a p = p * a ^ (p - 1) :=
have h : ∀ i ∈ finset.range p, a ^ ((i - 1) + (p - 1 - i)) * i = a ^ (p - 2) * i,
begin
  intros i hi,
  cases i,
  { rw [nat.cast_zero, mul_zero, mul_zero] },
  { congr' 2,
    rw ← nat.add_sub_assoc (nat.le_pred_of_lt (finset.mem_range.mp hi)),
    exact congr_arg nat.pred (nat.add_sub_cancel_left _ _) }
end,
calc  ∑ i in finset.range p, (a + p * b) ^ i * a ^ (p - 1 - i)
    = ∑ i in finset.range p,
        (a ^ i * a ^ (p - 1 - i) + b * p * (a ^ ((i - 1) + (p - 1 - i)) * i)) :
  finset.sum_congr rfl $ λ i hi, by rw add_mul_pow_eq hp2; ring_exp
... = p * a ^ (p - 1) + b * a ^ (p - 2) * ↑((p - 1) / 2) * ↑p ^ 2 :
  by rw [finset.sum_add_distrib, ← geom_sum₂, geom_sum₂_self, ← finset.mul_sum,
    finset.sum_congr rfl h, ← finset.mul_sum, ← nat.cast_sum, finset.sum_range_id,
    nat.mul_div_assoc _ (nat.dvd_sub_of_mod_eq hp), nat.cast_mul]; ring
... = p * a ^ (p - 1) :
  by rw [hp2, mul_zero, add_zero]

end helpers

end comm_ring

namespace multiplicity

section integral_domain

open ideal ideal.quotient

variables {R : Type*} [integral_domain R] [@decidable_rel R (∣)]

lemma pow_sub_pow' {p : R} (hp : prime p)
  {x y : R} (hxy₁ : p ∣ x - y) (hxy₂ : ¬p ∣ x * y)
  {n : ℕ} (hn : ¬p ∣ n) :
  multiplicity p (x ^ n - y ^ n) = multiplicity p (x - y) :=
by rw [← geom_sum₂_mul, multiplicity.mul hp,
  geom_sum₂_eq_zero hp hxy₁ hxy₂ hn, zero_add]

variables {p : ℕ} (hp : prime (p : R)) (hp1 : p % 2 = 1)
  {x y : R} (hxy₁ : ↑p ∣ x - y) (hxy₂ : ¬↑p ∣ x * y)
include hp hp1 hxy₁ hxy₂

lemma geom_sum₂_eq_one : multiplicity ↑p (geom_sum₂ x y p) = 1 :=
begin
  apply multiplicity.eq_some_iff.mpr,
  split,
  { rw ← mem_span_singleton at *,
    rw ← ideal.quotient.eq at hxy₁,
    rw [pow_one, ← eq_zero_iff_mem, ring_hom.map_geom_sum₂, hxy₁, geom_sum₂_self],
    apply mul_eq_zero_of_left,
    rw [← ring_hom.map_nat_cast (mk _), eq_zero_iff_mem, mem_span_singleton] },
  { let I : ideal R := span {p ^ 2},
    have hp' : (p : I.quotient) ^ 2 = 0,
    { rw [← ring_hom.map_nat_cast (mk I), ← ring_hom.map_pow,
        eq_zero_iff_mem, mem_span_singleton] },
    cases hxy₁ with k hk,
    rw [← mem_span_singleton, ← eq_zero_iff_mem, ring_hom.map_geom_sum₂,
      sub_eq_iff_eq_add'.mp hk, ring_hom.map_add, ring_hom.map_mul, ring_hom.map_nat_cast,
      geom_sum₂_add_mul hp' hp1, ← ring_hom.map_nat_cast (mk I),
      ← ring_hom.map_pow, ← ring_hom.map_mul, eq_zero_iff_mem,
      mem_span_singleton, pow_two, mul_dvd_mul_iff_left hp.1],
    intro h,
    exact hxy₂ (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h) _) }
end

lemma pow_prime_sub_pow_prime :
  multiplicity ↑p (x ^ p - y ^ p) = multiplicity ↑p (x - y) + 1 :=
by rw [← geom_sum₂_mul, multiplicity.mul hp,
    geom_sum₂_eq_one hp hp1 hxy₁ hxy₂, add_comm]

lemma pow_prime_pow_sub_pow_prime_pow (a : ℕ) :
  multiplicity ↑p (x ^ p ^ a - y ^ p ^ a) = multiplicity ↑p (x - y) + a :=
begin
  induction a with a h_ind,
  { rw [enat.coe_zero, add_zero, pow_zero, pow_one, pow_one] },
  rw [← nat.add_one, enat.coe_add, enat.coe_one, ← add_assoc,
    ← h_ind, pow_succ', pow_mul, pow_mul],
  apply pow_prime_sub_pow_prime hp hp1,
  { rw ← geom_sum₂_mul,
    exact dvd_mul_of_dvd_right hxy₁ _ },
  { rw ← mul_pow,
    intro h,
    exact hxy₂ (hp.dvd_of_dvd_pow h) }
end

end integral_domain

section lifting_the_exponent

variables {p : ℕ} (hp : p.prime) (hp1 : p % 2 = 1)
include hp hp1

/-- **Lifting the exponent lemma** for odd primes -/
theorem int.pow_sub_pow {x y : ℤ} (hxy₁ : ↑p ∣ x - y) (hxy₂ : ¬↑p ∣ x * y) (n : ℕ) :
  multiplicity ↑p (x ^ n - y ^ n) = multiplicity ↑p (x - y) + multiplicity p n :=
begin
  cases n,
  { rw [multiplicity.zero, add_top, pow_zero, pow_zero, sub_self, multiplicity.zero] },
  have h : (multiplicity _ _).dom := finite_nat_iff.mpr ⟨hp.ne_one, n.succ_pos⟩,
  rcases eq_some_iff.mp (enat.coe_get h).symm with ⟨⟨k, hk⟩, hpn⟩,
  conv_lhs { rw [hk, pow_mul, pow_mul] },
  rw nat.prime_iff_prime_int at hp,
  rw ← int.nat_cast_eq_coe_nat at *,
  rw [pow_sub_pow' hp, pow_prime_pow_sub_pow_prime_pow hp hp1 hxy₁ hxy₂, enat.coe_get],
  { rw ← geom_sum₂_mul,
    exact dvd_mul_of_dvd_right hxy₁ _ },
  { rw ← mul_pow,
    intro h,
    exact hxy₂ (hp.dvd_of_dvd_pow h) },
  { iterate 2 { rw int.nat_cast_eq_coe_nat },
    rw int.coe_nat_dvd,
    rintro ⟨c, rfl⟩,
    refine hpn ⟨c, _⟩,
    rw [pow_succ', mul_assoc, ← hk] }
end

theorem int.pow_add_pow {x y : ℤ} (hxy₁ : ↑p ∣ x + y) (hxy₂ : ¬↑p ∣ x * y)
  {n : ℕ} (hn : odd n) :
  multiplicity ↑p (x ^ n + y ^ n) = multiplicity ↑p (x + y) + multiplicity p n :=
begin
  rw ← sub_neg_eq_add at hxy₁,
  rw [← dvd_neg, neg_mul_eq_mul_neg] at hxy₂,
  rw [← sub_neg_eq_add, ← sub_neg_eq_add, ← nat.neg_pow_of_odd hn],
  exact int.pow_sub_pow hp hp1 hxy₁ hxy₂ n
end

theorem nat.pow_sub_pow {x y : ℕ} (hxy : y ≤ x)
  (hxy₁ : p ∣ x - y) (hxy₂ : ¬p ∣ x * y) (n : ℕ) :
  multiplicity p (x ^ n - y ^ n) = multiplicity p (x - y) + multiplicity p n :=
begin
  iterate 2 { rw ← int.coe_nat_multiplicity },
  rw [int.coe_nat_sub (nat.pow_le_pow_of_le_left hxy n),
    int.coe_nat_pow, int.coe_nat_pow],
  rw ← int.coe_nat_dvd at hxy₁ hxy₂,
  rw int.coe_nat_sub hxy at hxy₁ ⊢,
  rw int.coe_nat_mul at hxy₂,
  exact int.pow_sub_pow hp hp1 hxy₁ hxy₂ n
end

theorem nat.pow_add_pow {x y : ℕ} (hxy₁ : p ∣ x + y) (hxy₂ : ¬p ∣ x * y)
  {n : ℕ} (hn : odd n) :
  multiplicity p (x ^ n + y ^ n) = multiplicity p (x + y) + multiplicity p n :=
begin
  iterate 2 { rw [← int.coe_nat_multiplicity, int.coe_nat_add, int.coe_nat_pow] },
  rw ← int.coe_nat_dvd at hxy₁ hxy₂,
  rw int.coe_nat_add at hxy₁,
  rw int.coe_nat_mul at hxy₂,
  exact int.pow_add_pow hp hp1 hxy₁ hxy₂ hn
end

end lifting_the_exponent

end multiplicity

namespace padic_val_nat

section

variables {p : ℕ} [hp : fact p.prime] (hp1 : p % 2 = 1) {x y : ℕ}
include hp hp1

theorem pow_sub_pow (hxy : y < x) (hxy₁ : p ∣ x - y) (hxy₂ : ¬p ∣ x * y)
  {n : ℕ} (hn : 0 < n) :
  padic_val_nat p (x ^ n - y ^ n) = padic_val_nat p (x - y) + padic_val_nat p n :=
begin
  iterate 3 { rw padic_val_nat_def },
  { rw [← enat.coe_inj, enat.coe_add],
    iterate 3 { rw enat.coe_get },
    exact multiplicity.nat.pow_sub_pow hp.out hp1 hxy.le hxy₁ hxy₂ n },
  all_goals { apply ne_of_gt },
  { exact hn },
  { exact nat.sub_pos_of_lt hxy },
  { exact nat.sub_pos_of_lt (nat.pow_lt_pow_of_lt_left hxy hn) }
end

theorem pow_add_pow (hxy₁ : p ∣ x + y) (hxy₂ : ¬p ∣ x * y)
  {n : ℕ} (hn : odd n) :
  padic_val_nat p (x ^ n + y ^ n) = padic_val_nat p (x + y) + padic_val_nat p n :=
begin
  cases y,
  { exfalso, exact hxy₂ (dvd_zero _) },
  iterate 3 { rw padic_val_nat_def },
  { rw [← enat.coe_inj, enat.coe_add],
    iterate 3 { rw enat.coe_get },
    exact multiplicity.nat.pow_add_pow hp.out hp1 hxy₁ hxy₂ hn },
  { exact ne_of_gt (nat.odd_gt_zero hn) },
  { exact nat.succ_ne_zero _ },
  { exact ne_of_gt (nat.lt_add_left _ _ _ (pow_pos y.succ_pos _)) }
end

end

end padic_val_nat
