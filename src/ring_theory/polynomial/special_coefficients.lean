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
-/

open_locale polynomial
namespace polynomial

open polynomial nat
open_locale polynomial

variables {R : Type*} [semiring R] {a : R} {p q r : R[X]} {m n : ℕ}

/-- `ptl` is an auxilliary definition whose only purpose is to prove
lemma `coeff_mul_nat_degree_add_sub_one`.  Intuitively, if `p q : R[X]` are polynomials of
respecitve degrees `m` and `n`, then `plt m n p q` is the coefficient of the monomial
`X ^ (m + n - 1)` in the product `p * q`.  We have the extra flexibility of allowing arbitrary
`m` and `n`.  Moreover, in the edge cases where `m` or `n` equal `0` the intuitive interpretation
also fails.  -/
def ptl (m n : ℕ) (p q : R[X]) : R :=
p.coeff m * q.coeff (n - 1) + p.coeff (m - 1) * q.coeff n

namespace ptl

@[simp] lemma zero_left : ptl m n 0 q = 0 :=
by simp [ptl]

@[simp] lemma zero_right : ptl m n p 0 = 0 :=
by simp [ptl]

@[simp] lemma add_left : ptl m n (p + r) q = ptl m n p q + ptl m n r q :=
begin
  rw [ptl, ptl, ptl, coeff_add, coeff_add, add_mul, add_mul],
  abel
end

@[simp] lemma add_right : ptl m n p (q + r) = ptl m n p q + ptl m n p r :=
begin
  rw [ptl, ptl, ptl, coeff_add, coeff_add, mul_add, mul_add],
  abel
end

@[simp] lemma C_mul_left : ptl m n (C a * p) q = a * ptl m n p q :=
by simp only [ptl, mul_add, mul_assoc, coeff_C_mul]

@[simp] lemma C_mul_right : ptl m n p (q * C a) = ptl m n p q * a:=
by simp only [ptl, add_mul, mul_assoc, coeff_mul_C]

@[simp] lemma mul_X_left (p : R[X]) (m0 : m ≠ 0) :
  ptl (m + 1) n (p * X) q = ptl m n p q :=
begin
  rw [ptl, coeff_mul_X, add_comm m, nat.add_sub_assoc, add_comm 1, coeff_mul_X, ptl],
  exact nat.one_le_iff_ne_zero.mpr m0
end

@[simp] lemma mul_X_right (p : R[X]) (n0 : n ≠ 0) :
  ptl m (n + 1) p (q * X) = ptl m n p q :=
begin
  rw [ptl, nat.add_sub_cancel, ← nat.sub_add_cancel (_ : 1 ≤ n), coeff_mul_X, coeff_mul_X,
    nat.sub_add_cancel, ← ptl],
  repeat { exact nat.one_le_iff_ne_zero.mpr n0 }
end

@[simp] lemma mul_X_pow_left (m0 : m ≠ 0) :
  ∀ a : ℕ, ptl (m + a) n (p * X ^ a) q = ptl m n p q
| 0       := by rw [add_zero, pow_zero, mul_one]
| (a + 1) := by { rw [pow_add, ← mul_assoc, pow_one, ← add_assoc, mul_X_left],
                  { exact mul_X_pow_left _ },
                  { exact (nat.add_pos_left (nat.one_le_iff_ne_zero.mpr m0) _).ne' } }

@[simp] lemma mul_X_pow_right (n0 : n ≠ 0) :
  ∀ a : ℕ, ptl m (n + a) p (q * X ^ a) = ptl m n p q
| 0       := by rw [add_zero, pow_zero, mul_one]
| (a + 1) := by { rw [pow_add, ← mul_assoc, pow_one, ← add_assoc, mul_X_right],
                  { exact mul_X_pow_right _ },
                  { exact (nat.add_pos_left (nat.one_le_iff_ne_zero.mpr n0) _).ne' } }

lemma eq_right
  (hp : p.nat_degree ≠ 0) (hq : q.nat_degree ≠ 0) (pm : p.nat_degree ≤ m) (qn : q.nat_degree ≤ n) :
  (p * q).coeff (m + n - 1) = ptl m n p q :=
begin
  unfold ptl,
  refine induction_with_nat_degree_le (λ q, (p * q).coeff (m + n - 1) = ptl m n p q) n _ _ _ _ qn,
  { simp only [mul_zero, coeff_zero, zero_right] },
  { intros a r r0 an,
    have n1 : 1 ≤ n := (nat.one_le_iff_ne_zero.mpr hq).trans qn,
    have : n - 1 ≠ n := (nat.pred_lt (nat.one_le_iff_ne_zero.mp (n1))).ne,
    rw [← X_pow_mul, ← mul_assoc, coeff_mul_C, C_mul_right, ptl],
    apply congr_arg (* r),
    by_cases ae : a = n,
    { rw [ae, coeff_X_pow, if_neg this, coeff_X_pow, if_pos rfl, mul_zero, zero_add, mul_one],
      convert coeff_mul_X_pow _ _ _,
      rw [add_comm, nat.add_sub_assoc, add_comm],
      exact le_trans (nat.add_one_le_iff.mpr (nat.pos_of_ne_zero hp)) pm },
    by_cases a1 : a = n - 1,
    { simp [coeff_X_pow, a1, this.symm, nat.add_sub_assoc n1] },
    { suffices : (p * X ^ a).coeff (m + n - 1) = 0, { simpa [coeff_X_pow, ne.symm a1, ne.symm ae] },
      refine coeff_eq_zero_of_nat_degree_lt (nat_degree_mul_le.trans_lt _),
      rw nat.add_sub_assoc n1,
      refine add_lt_add_of_le_of_lt pm (nat_degree_pow_le.trans_lt (mul_lt_of_lt_of_le_one _ _)),
      { exact (le_pred_of_lt (an.lt_of_ne ae)).lt_of_ne a1 },
      { exact nat_degree_X_le } } },
  { exact λ f g fg gn hf hg, by simp [mul_add, hf, hg] }
end

end ptl

/--  `coeff_mul_nat_degree_add_sub_one` computes the coefficient of the term of degree one less
than the expected `nat_degree` of a product of polynomials.  If

* `p = p₀ * x ^ m + p₁ * x ^ (m - 1) + (...) : R[X]` and
* `q = q₀ * x ^ n + q₁ * x ^ (m - 1) + (...)`,

then the lemmas shows that `p₀ * q₁ + p₁ * q₀` equals `r₁ : R`  in

`p * q = r₀ * x ^ (m + n) + r₁ * x ^ (m + n - 1) + (...)`.   -/
lemma coeff_mul_nat_degree_add_sub_one (hp : p.nat_degree ≠ 0) (hq : q.nat_degree ≠ 0) :
  (p * q).coeff (p.nat_degree + q.nat_degree - 1) =
    p.leading_coeff * q.coeff (q.nat_degree - 1) + p.coeff (p.nat_degree - 1) * q.leading_coeff :=
ptl.eq_right hp hq rfl.le rfl.le

end polynomial
