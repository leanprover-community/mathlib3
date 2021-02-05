/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import analysis.transcendental.liouville
import data.nat.factorial

/-!
# Liouville constants

This files contains a construction of a family of Liouville number.
The most important property is that they are examples of transcendental real numbers.
This fact is recorded in `is_liouville.is_transcendental_of_liouville_constant`.
-/

namespace is_liouville

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

section natural
open nat

lemma add_le_mul_two_add {R : Type*} [ordered_semiring R] {a b : R}
  (a2 : 2 ≤ a) (b0 : 0 ≤ b) : a + (2 + b) ≤ a * (2 + b) :=
calc a + (2 + b) ≤ a + (a + a * b) :
      add_le_add_left (add_le_add a2 (le_mul_of_one_le_left b0 (one_le_two.trans a2))) a
             ... ≤ a * (2 + b) :
      ((add_assoc a a _).symm.le.trans (rfl.ge.trans (add_le_add_right
        (mul_two a).symm.le _))).trans (mul_add a 2 b).symm.le

lemma add_le_mul {a b : ℕ} (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ a * b :=
begin
  rcases le_iff_exists_add.mp b2 with ⟨k, rfl⟩,
  exact add_le_mul_two_add a2 k.zero_le
end

end natural

lemma add_factorial_le_factorial_add (i : ℕ) (n : ℕ) :
  i + (n + 1)! ≤ (i + (n + 1))! :=
begin
  by_cases i2 : 2 ≤ i,
  { exact (n.add_factorial_lt_factorial_add i2).le },
  { cases not_le.mp i2 with _ i0,
    { change 1 + (n + 1)! ≤ (1 + n + 1) * (1 + n)!,
      rw [add_mul, one_mul, add_comm 1 n],
      exact (add_le_add_iff_right _).mpr (one_le_mul (nat.le_add_left 1 n) (n + 1).factorial_pos) },
    { rw [nat.le_zero_iff.mp (nat.succ_le_succ_iff.mp i0), zero_add, zero_add] } }
end

/--  Partial inequality, works with `m ∈ ℝ` satisfying `1 < m`. -/
lemma calc_liou_one (m1 : 1 < m) (n : ℕ) :
∑' (i : ℕ), 1 / m ^ (i + (n + 1))! < m / (m - 1) * (1 / m ^ (n + 1)!) :=
have m0 : 0 < m := (zero_lt_one.trans m1),
have mi : abs (1 / m) < 1,
{ rw abs_of_pos (one_div_pos.mpr m0),
  exact (div_lt_one m0).mpr m1 },
calc (∑' i, 1 / m ^ (i + (n + 1))!)
    < ∑' i, 1 / m ^ (i + (n + 1)!) : begin refine tsum_lt_tsum_of_nonneg
    (λ b, one_div_nonneg.mpr (pow_nonneg m0.le _))
    (λ b, (one_div_le_one_div (pow_pos m0 _) (pow_pos m0 _)).mpr
      (pow_le_pow m1.le (add_factorial_le_factorial_add b n))) _
      (summable_inv_pow_ge m1 (λ j, nat.le.intro rfl)),
    { exact 2 },
    { refine (one_div_lt_one_div (pow_pos m0 _) (pow_pos m0 _)).mpr (pow_lt_pow m1 _),
      exact (n.add_factorial_lt_factorial_add rfl.le) }
  end
... = ∑' i, (1 / m) ^ i * (1 / m ^ (n + 1)!) :
    by { congr, ext i, rw [pow_add, div_pow, one_pow, ← div_div_eq_div_mul, div_eq_mul_one_div] }
... = (∑' i, (1 / m) ^ i) * (1 / m ^ (n + 1)!) : tsum_mul_right
... = m / (m - 1) * (1 / m ^ (n + 1)!) :
    by rw [tsum_geometric_of_abs_lt_1 mi, ← @inv_div _ _ _ m, sub_div, div_self (m0.ne.symm)]

lemma calc_liou_two_zero (n : ℕ) (hm : 2 ≤ m) :
  m / (m - 1) * (1 / m ^ (n + 1)!) ≤ 1 / (m ^ n!) ^ n :=
begin
  calc m / (m - 1) * (1 / m ^ (n + 1)!) ≤ 2 * (1 / m ^ (n + 1)!) : begin
    refine mul_le_mul _ rfl.le _ zero_le_two,
    { refine (div_le_iff (sub_pos.mpr (one_lt_two.trans_le hm))).mpr _,
      rw [mul_sub, mul_one, two_mul m],
      exact le_sub_iff_add_le.mpr ((add_le_add_iff_left _).mpr hm) },
    { exact one_div_nonneg.mpr (pow_nonneg (zero_le_two.trans hm) _) },
  end
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

/--
For a real number `m`, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for `1 < m`.  However, there is no restriction on `m`, since,
if the series does not converge, then the sum of the series is defined to be zero.
-/
def liouville_constant (m : ℝ) := ∑' (i : ℕ), 1 / m ^ i!

/--
`liouville_constant_first_k_terms` is the sum of the first `k` terms of Liouville's constant, i.e.
$$
\sum_{i=0}^k\frac{1}{m^{i!}}.
$$
-/
def liouville_constant_first_k_terms (m : ℝ) (k : ℕ) := ∑ i in range (k+1), 1 / m ^ i!

/--
`liouville_constant_terms_after_k` is the sum of the series of the terms in `liouville_constant m`
starting from `k+1`, i.e
$$
\sum_{i=k+1}^\infty\frac{1}{m^{i!}}.
$$
-/
def liouville_constant_terms_after_k (m : ℝ) (k : ℕ) :=  ∑' i, 1 / m ^ (i + (k+1))!

lemma liouville_constant_terms_after_pos (hm : 1 < m) :
  ∀ k, 0 < liouville_constant_terms_after_k m k := λ n,
calc 0 < 1 / m ^ (n + 1)! : one_div_pos.mpr (pow_pos (zero_lt_one.trans hm) _)
  ... = 1 / m ^ (0 + (n + 1))! : by rw zero_add
  ... ≤ ∑' (i : ℕ), 1 / m ^ (i + (n + 1))! :
      le_tsum (summable_inv_pow_n_add_fact _ hm) 0
        (λ i i0, one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _))

lemma liouville_constant_eq_first_k_terms_add_rest (hm : 1 < m) (k : ℕ):
  liouville_constant m = liouville_constant_first_k_terms m k +
  liouville_constant_terms_after_k m k :=
(sum_add_tsum_nat_add _ (summable_inv_pow_ge hm (λ i, i.self_le_factorial))).symm

end m_is_real


section m_is_natural

variable {m : ℕ}

lemma rat_of_liouville_constant_first_k_terms (hm : 1 < m) (k : ℕ) :
∃ p : ℕ, liouville_constant_first_k_terms m k = p / (m ^ k!) :=
begin
  induction k with k h,
  { exact ⟨1, by rw [liouville_constant_first_k_terms, range_one, sum_singleton, nat.cast_one]⟩ },
  { rcases h with ⟨p_k, h_k⟩,
    use p_k * (m ^ ((k + 1)! - k!)) + 1,
    unfold liouville_constant_first_k_terms at h_k ⊢,
    rw [sum_range_succ, h_k, div_add_div, div_eq_div_iff, one_mul, add_mul],
    { norm_cast,
      rw [add_mul, one_mul, nat.factorial_succ, show k.succ * k! - k! = (k.succ - 1) * k!,
        by rw [nat.mul_sub_right_distrib, one_mul], nat.succ_sub_one, nat.succ_eq_add_one, add_mul,
        one_mul, pow_add], ring },
    refine mul_ne_zero_iff.mpr ⟨_, _⟩,
    all_goals { exact pow_ne_zero _ (nat.cast_ne_zero.mpr ((zero_lt_one.trans hm).ne.symm)) } }
end

theorem is_liouville_liouville_constant (hm : 2 ≤ m) :
  is_liouville (liouville_constant m) :=
begin
  have mZ1 : 1 < (m : ℤ) := nat.cast_one.symm.le.trans_lt
    (one_lt_two.trans_le (nat.cast_two.symm.le.trans (int.to_nat_le.mp hm))),
  have m1 : 1 < (m : ℝ) :=
    one_lt_two.trans_le (nat.cast_two.symm.le.trans (nat.cast_le.mpr hm)),
  intro n,
  have mkk := liouville_constant_eq_first_k_terms_add_rest m1 n,
  rcases rat_of_liouville_constant_first_k_terms (one_lt_two.trans_le hm) n with ⟨p, hp⟩,
  refine ⟨p, m ^ n!, one_lt_pow mZ1 (nat.factorial_pos n), _⟩,
  push_cast,
  rw [← hp, mkk, add_sub_cancel', abs_of_pos (liouville_constant_terms_after_pos m1 _)],
  exact ⟨((lt_add_iff_pos_right _).mpr (liouville_constant_terms_after_pos m1 n)).ne.symm,
    (calc_liou_one m1 n).trans_le
    (calc_liou_two_zero _ (nat.cast_two.symm.le.trans (nat.cast_le.mpr hm)))⟩
end

lemma is_transcendental_liouville_constant (hm : 2 ≤ m) :
  is_transcendental ℤ (liouville_constant m) :=
transcendental_of_is_liouville (is_liouville_liouville_constant hm)

end m_is_natural

end is_liouville
