/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import data.polynomial.erase_lead
import data.polynomial.degree.lemmas

/-! # Computing special coefficients of polynomials

This file contains computations of certain, hopefully meaningful, coefficients of polynomials.

For instance, there is a computation of the coefficients "just before" the `leading_coeff`.

Let `R` be a (semi)ring.  We prove a formula for computing the previous-to-last coefficient of a
product of polynomials. -/

open_locale polynomial
namespace polynomial

open polynomial nat
open_locale polynomial

variables {R : Type*} [semiring R] {r : R} {f g h : R[X]} {a b c d : ℕ}

lemma coeff_mul_nat_degree_add_sub_one_le
  (f0 : f.nat_degree ≠ 0) (g0 : g.nat_degree ≠ 0) (fa : f.nat_degree ≤ a) (gb : g.nat_degree ≤ b) :
  (f * g).coeff (a + b - 1) = f.coeff a * g.coeff (b - 1) + f.coeff (a - 1) * g.coeff b :=
begin
  refine induction_with_nat_degree_le
    (λ q, (f * q).coeff (a + b - 1) =
      f.coeff a * q.coeff (b - 1) + f.coeff (a - 1) * q.coeff b) b _ _ _ _ gb,
  { simp only [mul_zero, coeff_zero, add_zero] },
  { intros n r r0 nb,
    have b1 : 1 ≤ b := (nat.one_le_iff_ne_zero.mpr g0).trans gb,
    have : b - 1 ≠ b := (nat.pred_lt (nat.one_le_iff_ne_zero.mp b1)).ne,
    rw [← X_pow_mul, ← mul_assoc, coeff_mul_C, coeff_mul_C, coeff_mul_C, ← mul_assoc, ← mul_assoc,
      ← add_mul],
    apply congr_arg (* r),
    by_cases bn : b = n,
    { rw [← bn, coeff_X_pow, if_neg this, coeff_X_pow, if_pos rfl, mul_zero, zero_add, mul_one],
      convert coeff_mul_X_pow _ _ _,
      rw [add_comm, nat.add_sub_assoc, add_comm],
      exact le_trans (nat.add_one_le_iff.mpr (nat.pos_of_ne_zero f0)) fa },
    by_cases a1 : n = b - 1,
    { simp [coeff_X_pow, a1, this.symm, nat.add_sub_assoc b1] },
    { suffices : (f * X ^ n).coeff (a + b - 1) = 0, { simpa [coeff_X_pow, ne.symm a1, bn] },
      refine coeff_eq_zero_of_nat_degree_lt (nat_degree_mul_le.trans_lt _),
      rw nat.add_sub_assoc b1,
      refine add_lt_add_of_le_of_lt fa (nat_degree_pow_le.trans_lt (mul_lt_of_lt_of_le_one _ _)),
      { exact (le_pred_of_lt (nb.lt_of_ne (ne.symm bn))).lt_of_ne a1 },
      { exact nat_degree_X_le } } },
  { exact λ p q fg gn hf hg, by simp [mul_add, hf, hg, add_add_add_comm] }
end

/--  `coeff_mul_nat_degree_add_sub_one` computes the coefficient of the term of degree one less
than the expected `nat_degree` of a product of polynomials.  If

* `f = f₀ * x ^ m + f₁ * x ^ (m - 1) + (...) : R[X]` and
* `g = g₀ * x ^ n + g₁ * x ^ (m - 1) + (...)`,

then the lemmas shows that `f₀ * g₁ + f₁ * g₀` equals `r₁ : R`  in

`f * g = r₀ * x ^ (m + n) + r₁ * x ^ (m + n - 1) + (...)`.   -/
lemma coeff_mul_nat_degree_add_sub_one (f0 : f.nat_degree ≠ 0) (g0 : g.nat_degree ≠ 0) :
  (f * g).coeff (f.nat_degree + g.nat_degree - 1) =
    f.leading_coeff * g.coeff (g.nat_degree - 1) + f.coeff (f.nat_degree - 1) * g.leading_coeff :=
coeff_mul_nat_degree_add_sub_one_le f0 g0 rfl.le rfl.le

end polynomial
