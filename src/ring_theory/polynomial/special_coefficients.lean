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

Let `R` be a (semi)ring.
We introduce the "previous-to-last" coefficient `ptl`, taking four natural numbers `a b c d : ℕ`
and two polynomials `f g : R[X]` as inputs.  We define
```lean
ptl a b c d f g = f.coeff a * g.coeff b + f.coeff c * g.coeff d.
```
This is intended simply as a helper definition to prove results without being constantly required
to prove that some natural number is positive, that some coefficient is non-zero, that some
polynomial has precisely some degree...  We develop enough API for `ptl` to essentially prove that
it is linear in either one of its polynomial inputs. -/

open_locale polynomial
namespace polynomial

open polynomial nat
open_locale polynomial

variables {R : Type*} [semiring R] {r : R} {f g h : R[X]} {a b c d : ℕ}

/-- "Previous-To-Last coefficient":

`ptl (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (f : R[X]) (g : R[X]) = f_a * g_b + f_c * g_d`,
where `p_i` is the `i`th coefficient of the polynomial `p`.
`ptl` is an auxilliary definition whose main purpose is to prove
lemma `coeff_mul_nat_degree_add_sub_one`.  The intended application is to compute
`(f * g)_(deg f + deg g - 1)`, the coefficient of `f * g` just before the top.  -/
def ptl (a b c d : ℕ) (f g : R[X]) : R :=
f.coeff a * g.coeff b + f.coeff c * g.coeff d

/-!  We prove lemmas showing linearity of `ptl` in its polynomial variables. -/
namespace ptl

@[simp] lemma zero_left : ptl a b c d 0 g = 0 :=
by simp [ptl]

@[simp] lemma zero_right : ptl a b c d f 0 = 0 :=
by simp [ptl]

@[simp] lemma add_left : ptl a b c d (f + h) g = ptl a b c d f g + ptl a b c d h g :=
by simp [ptl, add_mul, add_add_add_comm]

@[simp] lemma add_right : ptl a b c d f (g + h) = ptl a b c d f g + ptl a b c d f h :=
by simp [ptl, mul_add, add_add_add_comm]

@[simp] lemma C_mul_left : ptl a b c d (C r * f) g = r * ptl a b c d f g :=
by simp only [ptl, mul_add, mul_assoc, coeff_C_mul]

@[simp] lemma C_mul_right : ptl a b c d f (g * C r) = ptl a b c d f g * r:=
by simp only [ptl, add_mul, mul_assoc, coeff_mul_C]

@[simp] lemma mul_X_left (f : R[X]) :
  ptl (a + 1) b (c + 1) d (f * X) g = ptl a b c d f g :=
by rw [ptl, coeff_mul_X, coeff_mul_X, ptl]

@[simp] lemma mul_X_right (f : R[X]) :
  ptl a (b + 1) c (d + 1) f (g * X) = ptl a b c d f g :=
by rw [ptl, coeff_mul_X, coeff_mul_X, ← ptl]

@[simp] lemma mul_X_pow_left :
  ∀ n : ℕ, ptl (a + n) b (c + n) d (f * X ^ n) g = ptl a b c d f g
| 0       := by rw [add_zero, add_zero, pow_zero, mul_one]
| (n + 1) := by simp [pow_add, ← mul_assoc, ← add_assoc, mul_X_pow_left]

@[simp] lemma mul_X_pow_right :
  ∀ n : ℕ, ptl a (b + n) c (d + n) f (g * X ^ n) = ptl a b c d f g
| 0       := by rw [add_zero, add_zero, pow_zero, mul_one]
| (a + 1) := by simp [pow_add, ← mul_assoc, ← add_assoc, mul_X_pow_right]

lemma eq_right
  (f0 : f.nat_degree ≠ 0) (g0 : g.nat_degree ≠ 0) (fa : f.nat_degree ≤ a) (gb : g.nat_degree ≤ b) :
  (f * g).coeff (a + b - 1) = ptl a (b - 1) (a - 1) b f g :=
begin
  refine induction_with_nat_degree_le
    (λ q, (f * q).coeff (a + b - 1) = ptl a (b - 1) (a - 1) b f q) b _ _ _ _ gb,
  { simp only [mul_zero, coeff_zero, zero_right] },
  { intros n r r0 nb,
    have b1 : 1 ≤ b := (nat.one_le_iff_ne_zero.mpr g0).trans gb,
    have : b - 1 ≠ b := (nat.pred_lt (nat.one_le_iff_ne_zero.mp b1)).ne,
    rw [← X_pow_mul, ← mul_assoc, coeff_mul_C, C_mul_right, ptl],
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
  { exact λ f g fg gn hf hg, by simp [mul_add, hf, hg] }
end

end ptl

/--  `coeff_mul_nat_degree_add_sub_one` computes the coefficient of the term of degree one less
than the expected `nat_degree` of a product of polynomials.  If

* `f = f₀ * x ^ m + f₁ * x ^ (m - 1) + (...) : R[X]` and
* `g = g₀ * x ^ n + g₁ * x ^ (m - 1) + (...)`,

then the lemmas shows that `f₀ * g₁ + f₁ * g₀` equals `r₁ : R`  in

`f * g = r₀ * x ^ (m + n) + r₁ * x ^ (m + n - 1) + (...)`.   -/
lemma coeff_mul_nat_degree_add_sub_one (f0 : f.nat_degree ≠ 0) (g0 : g.nat_degree ≠ 0) :
  (f * g).coeff (f.nat_degree + g.nat_degree - 1) =
    f.leading_coeff * g.coeff (g.nat_degree - 1) + f.coeff (f.nat_degree - 1) * g.leading_coeff :=
ptl.eq_right f0 g0 rfl.le rfl.le

end polynomial
