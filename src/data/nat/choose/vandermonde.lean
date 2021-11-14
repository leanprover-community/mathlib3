/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.nat.choose.basic
import ring_theory.polynomial.basic

/-!

# Vandermonde's identity

In this file we prove Vandermonde's identity (`nat.add_choose_eq`):
`(m + n).choose k = ∑ (ij : ℕ × ℕ) in antidiagonal k, m.choose ij.1 * n.choose ij.2`

We follow the algebraic proof from
https://en.wikipedia.org/wiki/Vandermonde%27s_identity#Algebraic_proof .

-/

open_locale big_operators

open polynomial finset.nat

/-- Vandermonde's identity -/
lemma nat.add_choose_eq (m n k : ℕ) :
  (m + n).choose k = ∑ (ij : ℕ × ℕ) in antidiagonal k, m.choose ij.1 * n.choose ij.2 :=
begin
  calc (m + n).choose k
      = ((X + 1) ^ (m + n)).coeff k : _
  ... = ((X + 1) ^ m * (X + 1) ^ n).coeff k : by rw pow_add
  ... = ∑ (ij : ℕ × ℕ) in antidiagonal k, m.choose ij.1 * n.choose ij.2 : _,
  { rw [coeff_X_add_one_pow, nat.cast_id], },
  { rw [coeff_mul, finset.sum_congr rfl],
    simp only [coeff_X_add_one_pow, nat.cast_id, eq_self_iff_true, imp_true_iff], }
end
