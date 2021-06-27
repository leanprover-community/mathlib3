/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import tactic.interval_cases
import algebra.big_operators.order
import algebra.big_operators.enat
import data.nat.multiplicity

/-!
# IMO 2019 Q4

Find all pairs `(k, n)` of positive integers such that
```
  k! = (2 ^ n − 1)(2 ^ n − 2)(2 ^ n − 4)···(2 ^ n − 2 ^ (n − 1))
```
We show in this file that this property holds iff `(k, n) = (1, 1) ∨ (k, n) = (3, 2)`.

Proof sketch:
The idea of the proof is to count the factors of 2 on both sides. The LHS has less than `k` factors
of 2, and the RHS has exactly `n * (n - 1) / 2` factors of 2. So we know that `n * (n - 1) / 2 < k`.
Now for `n ≥ 6` we have `RHS < 2 ^ (n ^ 2) < (n(n-1)/2)! < k!`. We then treat the cases `n < 6`
individually.
-/

open_locale nat big_operators
open finset multiplicity nat (hiding zero_le prime)

theorem imo2019_q4_upper_bound {k n : ℕ} (hk : k > 0)
  (h : (k! : ℤ) = ∏ i in range n, (2 ^ n - 2 ^ i)) : n < 6 :=
begin
  have prime_2 : prime (2 : ℤ),
  { exact prime_iff_prime_int.mp prime_two },
  have h2 : n * (n - 1) / 2 < k,
  { suffices : multiplicity 2 (k! : ℤ) = (n * (n - 1) / 2 : ℕ),
    { rw [← enat.coe_lt_coe, ← this], change multiplicity ((2 : ℕ) : ℤ) _ < _,
      simp_rw [int.coe_nat_multiplicity, multiplicity_two_factorial_lt hk.lt.ne.symm] },
    rw [h, multiplicity.finset.prod prime_2, ← sum_range_id, ← sum_nat_coe_enat],
    apply sum_congr rfl, intros i hi,
    rw [multiplicity_sub_of_gt, multiplicity_pow_self_of_prime prime_2],
    rwa [multiplicity_pow_self_of_prime prime_2, multiplicity_pow_self_of_prime prime_2,
      enat.coe_lt_coe, ←mem_range] },
  rw [←not_le], intro hn,
  apply ne_of_lt _ h.symm,
  suffices : (∏ i in range n, 2 ^ n : ℤ) < ↑k!,
  { apply lt_of_le_of_lt _ this, apply prod_le_prod,
    { intros, rw [sub_nonneg], apply pow_le_pow, norm_num, apply le_of_lt, rwa [← mem_range] },
    { intros, apply sub_le_self, apply pow_nonneg, norm_num } },
  suffices : 2 ^ (n * n) < (n * (n - 1) / 2)!,
  { rw [prod_const, card_range, ← pow_mul], rw [← int.coe_nat_lt_coe_nat_iff] at this,
    clear h, convert this.trans _, norm_cast, rwa [int.coe_nat_lt_coe_nat_iff, factorial_lt],
    refine nat.div_pos _ (by norm_num),
    refine le_trans _ (mul_le_mul hn (pred_le_pred hn) (zero_le _) (zero_le _)),
    norm_num },
  refine le_induction _ _ n hn, { norm_num },
  intros n' hn' ih,
  have h5 : 1 ≤ 2 * n', { linarith },
  have : 2 ^ (2 + 2) ≤ (n' * (n' - 1) / 2).succ,
  { change succ (6 * (6 - 1) / 2) ≤ _,
    apply succ_le_succ, apply nat.div_le_div_right,
    exact mul_le_mul hn' (pred_le_pred hn') (zero_le _) (zero_le _) },
  rw [triangle_succ], apply lt_of_lt_of_le _ factorial_mul_pow_le_factorial,
  refine lt_of_le_of_lt _ (mul_lt_mul ih (nat.pow_le_pow_of_le_left this _)
    (pow_pos (by norm_num) _) (zero_le _)),
  rw [← pow_mul, ← pow_add], apply pow_le_pow_of_le_right, norm_num,
  rw [add_mul 2 2],
  convert add_le_add_left (add_le_add_left h5 (2 * n')) (n' * n') using 1, ring
end

theorem imo2019_q4 {k n : ℕ} (hk : k > 0) (hn : n > 0) :
  (k! : ℤ) = (∏ i in range n, (2 ^ n - 2 ^ i)) ↔ (k, n) = (1, 1) ∨ (k, n) = (3, 2) :=
begin
  /- The implication `←` holds. -/
  split, swap,
  { rintro (h|h); simp [prod.ext_iff] at h; rcases h with ⟨rfl, rfl⟩;
    norm_num [prod_range_succ, succ_mul] },
  intro h,
  /- We know that n < 6. -/
  have := imo2019_q4_upper_bound hk h,
  interval_cases n,
  /- n = 1 -/
  { left, congr, norm_num at h, norm_cast at h, rw [factorial_eq_one] at h, apply antisymm h,
    apply succ_le_of_lt hk },
  /- n = 2 -/
  { right, congr, norm_num [prod_range_succ] at h, norm_cast at h, rw [← factorial_inj],
    exact h, rw [h], norm_num },
  all_goals { exfalso, norm_num [prod_range_succ] at h, norm_cast at h, },
  /- n = 3 -/
  { refine monotone_factorial.ne_of_lt_of_lt_nat 5 _ _ _ h; norm_num },
  /- n = 4 -/
  { refine monotone_factorial.ne_of_lt_of_lt_nat 7 _ _ _ h; norm_num },
  /- n = 5 -/
  { refine monotone_factorial.ne_of_lt_of_lt_nat 10 _ _ _ h; norm_num },
end
