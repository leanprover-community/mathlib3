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

variable (hm : 1 < m)

include hm

/-- An easy criterion for convergence of a series. -/
lemma summable_inv_pow_ge {ex : ℕ → ℕ} (exi : ∀ i, i ≤ ex i) :
  summable (λ i, 1 / (m : ℝ) ^ ex i) :=
begin
  refine summable_of_nonneg_of_le
    (λ a, one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _)) (λ a, _)
    (summable_geometric_of_lt_1 (one_div_nonneg.mpr (zero_le_one.trans hm.le))
      ((one_div_lt (zero_lt_one.trans hm) zero_lt_one).mpr (by rwa one_div_one))),
  rw [div_pow, one_pow],
  refine (one_div_le_one_div _ _).mpr (pow_le_pow hm.le (exi a)),
  repeat { exact pow_pos (zero_lt_one.trans hm) _ },
end

/-- This series is explicitly proven, since it is used twice in the remaining lemmas. -/
lemma summable_inv_pow_n_add_fact (n : ℕ) :
  summable (λ i, 1 / (m : ℝ) ^ (i + (n + 1))!) :=
summable_inv_pow_ge hm (λ i, (nat.self_le_factorial _).trans (nat.factorial_le (nat.le.intro rfl)))

omit hm

/--  Partial inequality, works with `m ∈ ℝ` and satisfying `1 < m`. -/
lemma calc_liou_one (m1 : 1 < m) (n : ℕ) :
∑' (i : ℕ), 1 / m ^ (i + (n + 1))! ≤ m / (m - 1) * (1 / m ^ (n + 1)!) :=
have m0 : 0 < m := (lt_trans zero_lt_one m1),
have mi : abs (1 / m) < 1,
{ rw abs_of_pos (one_div_pos.mpr m0),
  exact (div_lt_one m0).mpr m1 },
calc (∑' i, 1 / (m : ℝ) ^ (i + (n + 1))!)
    ≤ ∑' i, 1 / (m : ℝ) ^ (i + (n + 1)!) :
    begin
      refine tsum_le_tsum (λ b, _) (summable_inv_pow_n_add_fact m1 _)
        (summable_of_nonneg_of_le (λ b, one_div_nonneg.mpr (pow_nonneg m0.le _))
        (λ b, _) (summable_geometric_of_abs_lt_1 mi)),
      { refine (one_div_le_one_div (pow_pos m0 _) (pow_pos m0 _)).mpr _,
        exact pow_le_pow m1.le (nat.add_factorial_le_factorial_add _ _ (nat.succ_ne_zero _)) },
      { rw [div_pow, one_pow, one_div_le_one_div],
        refine pow_le_pow m1.le (nat.le.intro rfl),
        repeat { exact pow_pos m0 _ } },
    end
... = ∑' i, (1 / m : ℝ) ^ i * (1 / m ^ (n + 1)!) :
    by { congr, ext i, rw [pow_add, div_pow, one_pow, ←div_div_eq_div_mul, div_eq_mul_one_div] }
... = (∑' i, (1 / m : ℝ) ^ i) * (1 / m ^ (n + 1)!) :
    begin
      rw tsum_mul_right,
    end
... = m / (m - 1) * (1 / m ^ (n + 1)!) :
    begin
      congr,
      rw [tsum_geometric_of_abs_lt_1 mi, show (m / (m - 1) : ℝ) = ((m - 1) / (m : ℝ))⁻¹,
        by rw inv_div, sub_div, div_self (ne_of_gt m0)]
    end

lemma calc_liou_two (n : ℕ) (hm : 2 < m) :
  m / (m - 1) * (1 / m ^ (n + 1)!) < 1 / (↑m ^ n!) ^ n :=
begin
  calc m / (m - 1) * (1 / m ^ (n + 1)!) < 2 * (1 / m ^ (n + 1)!) :
    begin
      refine mul_lt_mul _ le_rfl (one_div_pos.mpr (pow_pos (zero_lt_two.trans hm) _)) zero_le_two,
      rwa [div_lt_iff, mul_sub, mul_one, lt_sub_iff_add_lt, two_mul, real.add_lt_add_iff_left],
      exact lt_sub_iff_add_lt.mpr (by { rw zero_add, exact (one_lt_two.trans hm) })
    end
  ... = 2 / m ^ (n + 1)! : mul_one_div 2 _
  ... = 2 / m ^ (n! * (n + 1)) : by rw [nat.factorial_succ, mul_comm]
  ... < 1 / m ^ (n! * n) :
    begin
      rw [div_lt_div_iff, one_mul],
      conv_rhs { rw [mul_add, pow_add, mul_one, pow_mul, mul_comm] },
      apply mul_lt_mul,
      { refine lt_of_lt_of_le hm _,
        conv_lhs { rw ← pow_one m },
        exact pow_le_pow (one_le_two.trans hm.le) (nat.factorial_pos _) },
      { rw pow_mul },
      any_goals { try {refine le_of_lt _}, exact pow_pos (zero_lt_two.trans hm) _ }
    end
  ... = 1 / (m ^ n!) ^ n : by rw pow_mul
end

end lemmas_about_summability_and_sums

/--
liouville constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}
$$
where `2 < m`
-/
def liouville_constant (m : ℝ) := ∑' (i : ℕ), 1 / m ^ i!
/--
`liouville_constant_first_k_terms` is the first `k` terms of the liouville constant, i.e
$$
\sum_{i=0}^k\frac{1}{m^{i!}}
$$
where `2 < m`
-/
def liouville_constant_first_k_terms (m : ℝ) (k : ℕ) := ∑ i in range (k+1), 1 / m ^ i!
/--
`liouville_constant_terms_after_k` is all the terms start from `k+1` of the liouville constant, i.e
$$
\sum_{i=k+1}^\infty\frac{1}{m^{i!}}
$$
where `2 < m`
-/
def liouville_constant_terms_after_k (m : ℝ) (k : ℕ) :=  ∑' i, 1 / m ^ (i + (k+1))!

lemma liouville_constant_terms_after_pos (hm : 1 < m) :
  ∀ k, 0 < liouville_constant_terms_after_k m k := λ n,
calc 0 < 1 / (m : ℝ) ^ (n + 1)! : one_div_pos.mpr (pow_pos (lt_trans zero_lt_one hm) _)
  ... = 1 / (m : ℝ) ^ (0 + (n + 1))! : by rw zero_add
  ... ≤ ∑' (i : ℕ), 1 / (m : ℝ) ^ (i + (n + 1))! :
      le_tsum (summable_inv_pow_n_add_fact hm _) 0
        (λ i i0, one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _))

lemma liouville_constant_eq_first_k_terms_add_rest (hm : 1 < m) (k : ℕ):
  liouville_constant m = liouville_constant_first_k_terms m k +
  liouville_constant_terms_after_k m k :=
(sum_add_tsum_nat_add _ (summable_inv_pow_ge hm (λ i, nat.self_le_factorial i))).symm

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
    all_goals { refine pow_ne_zero _ _, exact_mod_cast ne_of_gt (lt_trans zero_lt_one hm), } }
end

theorem is_liouville_liouville_constant (hm : 2 < m) :
  is_liouville (liouville_constant m) :=
begin
  intro n,
  have h_truncation_wd := liouville_constant_eq_first_k_terms_add_rest
    (by exact_mod_cast lt_trans one_lt_two hm : 1 < (m : ℝ)) n,
  rcases rat_of_liouville_constant_first_k_terms (lt_trans one_lt_two hm) n with ⟨p, hp⟩,
  use [p, m ^ n!],
  push_cast,
  rw [← hp, h_truncation_wd, add_sub_cancel', abs_of_pos (liouville_constant_terms_after_pos
    (by exact_mod_cast lt_trans one_lt_two hm : 1 < (m : ℝ)) _)],
  refine ⟨one_lt_pow (by exact_mod_cast (lt_trans one_lt_two hm)) (nat.factorial_pos _),
    liouville_constant_terms_after_pos (by exact_mod_cast lt_trans one_lt_two hm) _, _⟩,
  refine lt_of_le_of_lt (calc_liou_one (by exact_mod_cast (lt_trans one_lt_two hm)) n) _,
  exact calc_liou_two _ (by assumption_mod_cast),
end

lemma is_transcendental_liouville_constant (hm : 2 < m) :
  is_transcendental ℤ (liouville_constant m) :=
transcendental_of_is_liouville (is_liouville_liouville_constant hm)

end m_is_natural

end is_liouville
