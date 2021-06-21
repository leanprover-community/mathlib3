/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jujian Zhang
-/
import analysis.liouville.basic
import analysis.liouville.inequalities_and_series
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

namespace liouville

/-
For a real number `m`, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for `1 < m`.  However, there is no restriction on `m`, since,
if the series does not converge, then the sum of the series is defined to be zero.
-/
def liouville_number (m : ℝ) : ℝ := ∑' (i : ℕ), 1 / m ^ i!

/--
`liouville_number_initial_terms` is the sum of the first `k + 1` terms of Liouville's constant,
i.e.
$$
\sum_{i=0}^k\frac{1}{m^{i!}}.
$$
-/
def liouville_number_initial_terms (m : ℝ) (k : ℕ) : ℝ := ∑ i in range (k+1), 1 / m ^ i!

/--
`liouville_number_tail` is the sum of the series of the terms in `liouville_number m`
starting from `k+1`, i.e
$$
\sum_{i=k+1}^\infty\frac{1}{m^{i!}}.
$$
-/
def liouville_number_tail (m : ℝ) (k : ℕ) : ℝ := ∑' i, 1 / m ^ (i + (k+1))!

lemma liouville_number_tail_pos (hm : 1 < m) (k : ℕ) :
  0 < liouville_number_tail m k :=
-- replace `0` with the constantly zero series `∑ i : ℕ, 0`
calc  (0 : ℝ) = ∑' i : ℕ, 0 : tsum_zero.symm
          ... < liouville_number_tail m k :
  -- to show that a series with non-negative terms has strictly positive sum it suffices
  -- to prove that
  tsum_lt_tsum_of_nonneg
    -- 1. the terms are the zero series are indeed non-negative
    (λ _, rfl.le)
    -- 2. the terms of our series are non-negative
    (λ i, one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _))
    -- 3. one term of our series is strictly positive -- they all are, we use the first term
    (one_div_pos.mpr (pow_pos (zero_lt_one.trans hm) (0 + (k + 1))!)) $
    -- 4. our series converges -- it does since it is the tail of a converging series, though
    -- this is not the argument here.
    summable_inv_pow_ge hm (λ i, i.self_le_factorial.trans (nat.factorial_le (nat.le.intro rfl)))

/--  Split the sum definining a Liouville number into the first `k` term and the rest. -/
lemma liouville_number_eq_initial_terms_add_tail (hm : 1 < m) (k : ℕ) :
  liouville_number m = liouville_number_initial_terms m k +
  liouville_number_tail m k :=
(sum_add_tsum_nat_add _ (summable_inv_pow_ge hm (λ i, i.self_le_factorial))).symm

end liouville

end m_is_real


section m_is_natural

variable {m : ℕ}

namespace liouville

/--  The sum of the `k` initial terms of the Liouville number to base `m` is a ratio of natural
numbers where the denominator is `m ^ k!`. -/
lemma liouville_number_rat_initial_terms (hm : 0 < m) (k : ℕ) :
∃ p : ℕ, liouville_number_initial_terms m k = p / m ^ k! :=
begin
  induction k with k h,
  { exact ⟨1, by rw [liouville_number_initial_terms, range_one, sum_singleton, nat.cast_one]⟩ },
  { rcases h with ⟨p_k, h_k⟩,
    use p_k * (m ^ ((k + 1)! - k!)) + 1,
    unfold liouville_number_initial_terms at h_k ⊢,
    rw [sum_range_succ, h_k, div_add_div, div_eq_div_iff, add_mul],
    { norm_cast,
      rw [add_mul, one_mul, nat.factorial_succ,
        show k.succ * k! - k! = (k.succ - 1) * k!, by rw [nat.mul_sub_right_distrib, one_mul],
        nat.succ_sub_one, nat.succ_eq_add_one, add_mul, one_mul, pow_add],
      simp [mul_assoc] },
    refine mul_ne_zero_iff.mpr ⟨_, _⟩,
    all_goals { exact pow_ne_zero _ (nat.cast_ne_zero.mpr hm.ne.symm) } }
end

lemma pre_sum_liouville {f : ℕ → ℕ} {m : ℝ} (hm : 1 < m) (f0 : ∀ n, 0 < f n)
  (fn1 : ∀ n, 2 * (f n) ^ n ≤ f (n + 1)) :
  summable (λ i, 1 / m ^ f i) :=
begin
  apply summable_inv_pow_ge hm,
  intros i,
  induction i with i hi,
  { exact zero_le (f 0) },
  cases i,
  { exact nat.succ_le_iff.mpr (f0 1) },
  refine trans _ (fn1 _),
  refine trans (nat.succ_le_succ hi) _,
  refine trans (add_one_le_two_mul (f0 _)) _,
  refine (mul_le_mul_left zero_lt_two).mpr _,
  calc  f i.succ = f i.succ ^ 1 : (pow_one _).symm
        ... ≤ f i.succ ^ i.succ : by {refine pow_le_pow _ (nat.succ_le_succ (zero_le i)),
        exact nat.succ_le_iff.mpr (f0 (nat.succ i)) }
end

theorem is_liouville (hm : 2 ≤ m) :
  liouville (liouville_number m) :=
begin
  -- two useful inequalities
  have mZ1 : 1 < (m : ℤ) := nat.cast_one.symm.le.trans_lt
    (one_lt_two.trans_le (nat.cast_two.symm.le.trans (int.to_nat_le.mp hm))),
  have m1 : 1 < (m : ℝ) :=
    one_lt_two.trans_le (nat.cast_two.symm.le.trans (nat.cast_le.mpr hm)),
  intro n,
  -- the first `n` terms sum to `p / m ^ k!`
  rcases liouville_number_rat_initial_terms (zero_lt_two.trans_le hm) n with ⟨p, hp⟩,
  refine ⟨p, m ^ n!, one_lt_pow mZ1 (nat.factorial_pos n), _⟩,
  push_cast,
  -- separate out the sum of the first `n` terms and the rest
  rw liouville_number_eq_initial_terms_add_tail m1 n,
  rw [← hp, add_sub_cancel', abs_of_nonneg (liouville_number_tail_pos m1 _).le],
  exact ⟨((lt_add_iff_pos_right _).mpr (liouville_number_tail_pos m1 n)).ne.symm,
    (calc_liou_one m1 n).trans_le
    (calc_liou_two_zero _ (nat.cast_two.symm.le.trans (nat.cast_le.mpr hm)))⟩
end

lemma is_transcendental (hm : 2 ≤ m) :
  _root_.transcendental ℤ (liouville_number m) :=
liouville.transcendental (is_liouville hm)

end liouville

end m_is_natural
