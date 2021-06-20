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
This fact is recorded in `is_liouville.is_transcendental_of_liouville_constant` (a result in
a subsequent PR).
-/

noncomputable theory
open_locale nat big_operators
open set real finset

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
    -- 1. the terms of the zero series are indeed non-negative
    (λ _, rfl.le)
    -- 2. the terms of our series are non-negative
    (λ i, one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _))
    -- 3. one term of our series is strictly positive -- they all are, we use the first term
    (one_div_pos.mpr (pow_pos (zero_lt_one.trans hm) (0 + (k + 1))!)) $
    -- 4. our series converges -- it does since it is the tail of a converging series, though
    -- this is not the argument here.
    summable_inv_pow_ge hm (λ i, trans le_self_add (nat.self_le_factorial _))

/--  Split the sum definining a Liouville number into the first `k` term and the rest. -/
lemma liouville_number_eq_initial_terms_add_tail (hm : 1 < m) (k : ℕ) :
  liouville_number m = liouville_number_initial_terms m k +
  liouville_number_tail m k :=
(sum_add_tsum_nat_add _ (summable_inv_pow_ge hm (λ i, i.self_le_factorial))).symm

end liouville

end m_is_real
