/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jujian Zhang
-/
import analysis.liouville.basic
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

end liouville

end m_is_real
