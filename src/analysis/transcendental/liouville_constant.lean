/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import analysis.transcendental.liouville
import data.nat.factorial
import order.basic

/-!
# Liouville constants

This file contains a construction of a family of Liouville numbers.
The most important property is that they are examples of transcendental real numbers.
This fact is recorded in `is_liouville.is_transcendental_of_liouville_constant`.
-/

noncomputable theory
open_locale nat big_operators
open set real finset

section m_is_real

variable {m : ℝ}

section lemmas_about_summability_and_sums

/-- A series whose terms are bounded by the terms of a converging geometric series convergences. -/
lemma summable_inv_pow_ge {f : ℕ → ℕ} (hm : 1 < m) (fi : ∀ i, i ≤ f i) :
  summable (λ i, 1 / m ^ f i) :=
begin
  refine summable_of_nonneg_of_le
    (λ a, one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _)) (λ a, _)
    (summable_geometric_of_lt_1 (one_div_nonneg.mpr (zero_le_one.trans hm.le))
      ((one_div_lt (zero_lt_one.trans hm) zero_lt_one).mpr (by rwa one_div_one))),
  rw [div_pow, one_pow],
  refine (one_div_le_one_div _ _).mpr (pow_le_pow hm.le (fi a)),
  repeat { exact pow_pos (zero_lt_one.trans hm) _ }
end

/-- This series is explicitly proven, since it is used twice in the remaining lemmas. -/
lemma summable_inv_pow_n_add_fact (n : ℕ) (hm : 1 < m) :
  summable (λ i, 1 / m ^ (i + (n + 1))!) :=
summable_inv_pow_ge hm (λ i, (nat.self_le_factorial _).trans (nat.factorial_le (nat.le.intro rfl)))

end lemmas_about_summability_and_sums

lemma one_div_pow_strict_mono_decr_on : strict_mono_decr_on (λ x : ℝ, 1 / x) (set.Ioi 0) :=
λ x x1 y y1 xy, (one_div_lt_one_div (mem_Ioi.mp y1) (mem_Ioi.mp x1)).mpr xy

lemma one_div_mono_exp (m1 : 1 ≤ m) {a b : ℕ} (ab : a ≤ b) :
  1 / m ^ b ≤ 1 / m ^ a :=
begin
  refine (one_div_le_one_div _ _).mpr (pow_le_pow m1 ab);
  exact pow_pos (lt_of_lt_of_le zero_lt_one m1) _
end

lemma one_div_pow_strict_mono (m1 : 1 < m) {a b : ℕ} (ab : a < b) :
  1 / m ^ b < 1 / m ^ a :=
begin
  refine one_div_pow_strict_mono_decr_on _ _ (pow_lt_pow m1 ab);
  exact pow_pos (zero_lt_one.trans m1) _
end

/-
lemma one_div_mono_base {x y : ℝ} (x0 : 0 < x) (xy : x < y) (n : ℕ) : 1 / x ^ n < 1 / y ^ n :=
sorry
begin
  apply (one_div_lt_one_div _ _).mpr _,
  apply pow_pos x0,
  apply pow_pos (x0.trans xy),
  apply pow_lt_pow,
  refine (one_div_lt_one_div (pow_pos x0 _) _).mpr _,
end
-/

lemma pre_calc_liou_one_le (m1 : 1 ≤ m) (n : ℕ) (i : ℕ) :
  1 / m ^ (i + (n + 1))! ≤ 1 / m ^ (i + (n + 1)!) :=
one_div_mono_exp m1 (i.add_factorial_succ_le_factorial_add_succ n)

lemma pre_calc_liou_one (m1 : 1 < m) (n : ℕ) {i : ℕ} (i2 : 2 ≤ i) :
  1 / m ^ (i + (n + 1))! < 1 / m ^ (i + (n + 1)!) :=
one_div_pow_strict_mono m1 (n.add_factorial_succ_lt_factorial_add_succ i2)

/--  Partial inequality, works with `m ∈ ℝ` satisfying `1 < m`. -/
lemma calc_liou_one (m1 : 1 < m) (n : ℕ) :
∑' (i : ℕ), 1 / m ^ (i + (n + 1))! < m / (m - 1) * (1 / m ^ (n + 1)!) :=
have m0 : 0 < m := (zero_lt_one.trans m1),
have mi : abs (1 / m) < 1,
{ rw abs_of_pos (one_div_pos.mpr m0),
  exact (div_lt_one m0).mpr m1 },
calc (∑' i, 1 / m ^ (i + (n + 1))!)
    < ∑' i, 1 / m ^ (i + (n + 1)!) : tsum_lt_tsum_of_nonneg
-- the first series has non-negative term
      (λ b, one_div_nonneg.mpr (pow_nonneg m0.le _))
-- the second series dominates the first
      (λ b, one_div_mono_exp m1.le (b.add_factorial_succ_le_factorial_add_succ n))
-- the second term of the first series is strictly smaller than the second term of the first
      (one_div_pow_strict_mono m1 (n.add_factorial_succ_lt_factorial_add_succ rfl.le))
-- the second series is summable
      (summable_inv_pow_ge m1 (λ j, nat.le.intro rfl))
... = ∑' i, (1 / m) ^ i * (1 / m ^ (n + 1)!) :
    by { congr, ext i, rw [pow_add, ← div_div_eq_div_mul, div_eq_mul_one_div, ← one_div_pow i] }
... = (∑' i, (1 / m) ^ i) * (1 / m ^ (n + 1)!) : tsum_mul_right
... = m / (m - 1) * (1 / m ^ (n + 1)!) :
    by rw [tsum_geometric_of_abs_lt_1 mi, ← @inv_div _ _ _ m, sub_div, div_self (m0.ne.symm)]

lemma ine (hm : 2 ≤ m) :
  m / (m - 1) ≤ 2 :=
begin
  refine (div_le_iff (sub_pos.mpr (one_lt_two.trans_le hm))).mpr _,
  rw [mul_sub, mul_one, two_mul m],
  exact le_sub_iff_add_le.mpr ((add_le_add_iff_left _).mpr hm)
end

lemma calc_liou_two_zero (n : ℕ) (hm : 2 ≤ m) :
  m / (m - 1) * (1 / m ^ (n + 1)!) ≤ 1 / (m ^ n!) ^ n :=
begin
  calc m / (m - 1) * (1 / m ^ (n + 1)!) ≤ 2 * (1 / m ^ (n + 1)!) :
    mul_mono_nonneg (one_div_nonneg.mpr (pow_nonneg (zero_le_two.trans hm) _)) (ine hm)
  ... = 2 / m ^ (n + 1)! : mul_one_div 2 _
  ... = 2 / m ^ (n! * (n + 1)) : by rw [nat.factorial_succ, mul_comm]
  ... ≤ 1 / m ^ (n! * n) :
    begin
      apply (div_le_div_iff _ _).mpr,
      conv_rhs { rw [one_mul, mul_add, pow_add, mul_one, pow_mul, mul_comm, ← pow_mul] },
      apply (mul_le_mul_right _).mpr,
      any_goals { exact pow_pos (zero_lt_two.trans_le hm) _ },
      refine le_trans (hm.trans _) (pow_mono (one_le_two.trans hm) n.factorial_pos),
      exact (pow_one _).symm.le
    end
  ... = 1 / (m ^ n!) ^ n : by rw pow_mul
end

namespace liouville

/--
For a real number `m`, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for `1 < m`.  However, there is no restriction on `m`, since,
if the series does not converge, then the sum of the series is defined to be zero.
-/
def number (m : ℝ) := ∑' (i : ℕ), 1 / m ^ i!

/--
`liouville_constant_first_k_terms` is the sum of the first `k` terms of Liouville's constant, i.e.
$$
\sum_{i=0}^k\frac{1}{m^{i!}}.
$$
-/
def number_first_k_terms (m : ℝ) (k : ℕ) := ∑ i in range (k+1), 1 / m ^ i!

/--
`liouville_constant_terms_after_k` is the sum of the series of the terms in `liouville_constant m`
starting from `k+1`, i.e
$$
\sum_{i=k+1}^\infty\frac{1}{m^{i!}}.
$$
-/
def number_terms_after_k (m : ℝ) (k : ℕ) :=  ∑' i, 1 / m ^ (i + (k+1))!

lemma number_terms_after_pos (hm : 1 < m) :
  ∀ k, 0 < number_terms_after_k m k := λ n,
calc 0 < 1 / m ^ (n + 1)! : one_div_pos.mpr (pow_pos (zero_lt_one.trans hm) _)
  ... = 1 / m ^ (0 + (n + 1))! : by rw zero_add
  ... ≤ ∑' (i : ℕ), 1 / m ^ (i + (n + 1))! : le_tsum
      (summable_inv_pow_n_add_fact _ hm)
      0
      (λ i i0, one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _))


lemma number_eq_first_k_terms_add_rest (hm : 1 < m) (k : ℕ):
  number m = number_first_k_terms m k +
  number_terms_after_k m k :=
(sum_add_tsum_nat_add _ (summable_inv_pow_ge hm (λ i, i.self_le_factorial))).symm

end liouville

end m_is_real


section m_is_natural

variable {m : ℕ}

namespace liouville

lemma number_rat_first_k_terms (hm : 1 < m) (k : ℕ) :
∃ p : ℕ, number_first_k_terms m k = p / (m ^ k!) :=
begin
  induction k with k h,
  { exact ⟨1, by rw [number_first_k_terms, range_one, sum_singleton, nat.cast_one]⟩ },
  { rcases h with ⟨p_k, h_k⟩,
    use p_k * (m ^ ((k + 1)! - k!)) + 1,
    unfold number_first_k_terms at h_k ⊢,
    rw [sum_range_succ, h_k, div_add_div, div_eq_div_iff, one_mul, add_mul],
    { norm_cast,
      rw [add_mul, one_mul, nat.factorial_succ, show k.succ * k! - k! = (k.succ - 1) * k!,
        by rw [nat.mul_sub_right_distrib, one_mul], nat.succ_sub_one, nat.succ_eq_add_one, add_mul,
        one_mul, pow_add], ring },
    refine mul_ne_zero_iff.mpr ⟨_, _⟩,
    all_goals { exact pow_ne_zero _ (nat.cast_ne_zero.mpr ((zero_lt_one.trans hm).ne.symm)) } }
end

theorem is_number (hm : 2 ≤ m) :
  liouville (number m) :=
begin
  have mZ1 : 1 < (m : ℤ) := nat.cast_one.symm.le.trans_lt
    (one_lt_two.trans_le (nat.cast_two.symm.le.trans (int.to_nat_le.mp hm))),
  have m1 : 1 < (m : ℝ) :=
    one_lt_two.trans_le (nat.cast_two.symm.le.trans (nat.cast_le.mpr hm)),
  intro n,
  have mkk := number_eq_first_k_terms_add_rest m1 n,
  rcases number_rat_first_k_terms (one_lt_two.trans_le hm) n with ⟨p, hp⟩,
  refine ⟨p, m ^ n!, one_lt_pow mZ1 (nat.factorial_pos n), _⟩,
  push_cast,
  rw [← hp, mkk, add_sub_cancel', abs_of_pos (number_terms_after_pos m1 _)],
  exact ⟨((lt_add_iff_pos_right _).mpr (number_terms_after_pos m1 n)).ne.symm,
    (calc_liou_one m1 n).trans_le
    (calc_liou_two_zero _ (nat.cast_two.symm.le.trans (nat.cast_le.mpr hm)))⟩
end

lemma is_transcendental (hm : 2 ≤ m) :
  is_transcendental ℤ (number m) :=
transcendental (is_number hm)

end liouville

end m_is_natural
