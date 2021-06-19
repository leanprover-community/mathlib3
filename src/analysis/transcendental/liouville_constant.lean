/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jujian Zhang
-/
import data.real.liouville
/-!
# Liouville constants

This file contains a construction of a family of Liouville numbers.
The most important property is that they are examples of transcendental real numbers.
This fact is recorded in `is_liouville.is_transcendental_of_liouville_constant`.
-/

noncomputable theory
open_locale nat big_operators
open set real finset

lemma summable_inv_pow_ge {m : ℝ} {f : ℕ → ℕ} (hm : 1 < m) (fi : ∀ i, i ≤ f i) :
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

section m_is_real

variable {m : ℝ}

namespace liouville

/--
For a real number `m`, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for `1 < m`.  However, there is no restriction on `m`, since,
if the series does not converge, then the sum of the series is defined to be zero.
-/
def liouville_number (m : ℝ) := ∑' (i : ℕ), 1 / m ^ i!

/--
`liouville_constant_first_k_terms` is the sum of the first `k` terms of Liouville's constant, i.e.
$$
\sum_{i=0}^k\frac{1}{m^{i!}}.
$$
-/
def liouville_number_first_k_terms (m : ℝ) (k : ℕ) := ∑ i in range (k+1), 1 / m ^ i!

/--
`liouville_constant_terms_after_k` is the sum of the series of the terms in `liouville_constant m`
starting from `k+1`, i.e
$$
\sum_{i=k+1}^\infty\frac{1}{m^{i!}}.
$$
-/
def liouville_number_terms_after_k (m : ℝ) (k : ℕ) :=  ∑' i, 1 / m ^ (i + (k+1))!

lemma liouville_number_terms_after_pos_ (hm : 1 < m) (k : ℕ) :
  0 < liouville_number_terms_after_k m k :=
-- replace `0` with the series `∑ i : ℕ, 0` all of whose terms vanish
(@tsum_zero _ ℕ _ _ _).symm.le.trans_lt (
  -- to show that a series with non-negative terms has strictly positive sum it suffices
  -- to prove that:
  tsum_lt_tsum_of_nonneg
    -- 1. the terms of the zero series are indeed non-negative [sic];
    (λ _, rfl.le)
    -- 2. the terms of our series are non-negative;
    (λ i, one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _))
    -- 3. one term of our series is strictly positive -- they all are, we use the `0`th term;
    (one_div_pos.mpr (pow_pos (zero_lt_one.trans hm) (0 + (k + 1))!))
    -- 4. our series converges -- it does since it is the tail ...
    ((@summable_nat_add_iff ℝ _ _ _ (λ (i : ℕ), 1 / m ^ i!) (k+1)).mpr
      -- ... of the converging series `∑ 1 / n!`.
      (summable_inv_pow_ge hm (λ i, i.self_le_factorial))))

--/-
lemma liouville_number_terms_after_pos (hm : 1 < m) (k : ℕ) :
  0 < liouville_number_terms_after_k m k :=
-- replace `0` with the constantly zero series `∑ i : ℕ, 0`
(@tsum_zero _ ℕ _ _ _).symm.le.trans_lt $
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
    summable_inv_pow_ge hm (λ i, trans (le_self_add) (nat.self_le_factorial _))

/--  Split the sum definining a Liouville number into the first `k` term and the rest. -/
lemma liouville_number_eq_first_k_terms_add_rest (hm : 1 < m) (k : ℕ) :
  liouville_number m = liouville_number_first_k_terms m k +
  liouville_number_terms_after_k m k :=
(sum_add_tsum_nat_add _ (summable_inv_pow_ge hm (λ i, i.self_le_factorial))).symm

end liouville

end m_is_real
