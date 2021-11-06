/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import analysis.special_functions.trigonometric.basic
import ring_theory.polynomial.chebyshev

/-!
# Multiple angle formulas in terms of Chebyshev polynomials

* `polynomial.chebyshev.T_complex_cos`: the `n`-th Chebyshev polynomial evaluates on `complex.cos θ`
  to the value `complex.cos (n * θ)`.
-/

namespace polynomial.chebyshev

open polynomial complex

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
lemma T_complex_cos (θ : ℂ) :
  ∀ n, (T ℂ n).eval (cos θ) = cos (n * θ)
| 0       := by simp only [T_zero, eval_one, nat.cast_zero, zero_mul, cos_zero]
| 1       := by simp only [eval_X, one_mul, T_one, nat.cast_one]
| (n + 2) :=
begin
  simp only [eval_X, eval_one, T_add_two, eval_sub, eval_bit0, nat.cast_succ, eval_mul],
  rw [T_complex_cos (n + 1), T_complex_cos n],
  have aux : sin θ * sin θ = 1 - cos θ * cos θ,
  { rw ← sin_sq_add_cos_sq θ, ring, },
  simp only [nat.cast_add, nat.cast_one, add_mul, cos_add, one_mul, sin_add, mul_assoc, aux],
  ring,
end

/-- `cos (n * θ)` is equal to the `n`-th Chebyshev polynomial of the first kind evaluated
on `cos θ`. -/
lemma cos_nat_mul (n : ℕ) (θ : ℂ) :
  cos (n * θ) = (T ℂ n).eval (cos θ) :=
(T_complex_cos θ n).symm

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n+1) * θ) / sin θ`. -/
lemma U_complex_cos (θ : ℂ) (n : ℕ) :
  (U ℂ n).eval (cos θ) * sin θ = sin ((n+1) * θ) :=
begin
  induction n with d hd,
  { simp only [U_zero, nat.cast_zero, eval_one, mul_one, zero_add, one_mul] },
  { rw U_eq_X_mul_U_add_T,
    simp only [eval_add, eval_mul, eval_X, T_complex_cos, add_mul, mul_assoc, hd, one_mul],
    conv_rhs { rw [sin_add, mul_comm] },
    push_cast,
    simp only [add_mul, one_mul] }
end

/-- `sin ((n + 1) * θ)` is equal to `sin θ` multiplied with the `n`-th Chebyshev polynomial of the
second kind evaluated on `cos θ`. -/
lemma sin_nat_succ_mul (n : ℕ) (θ : ℂ) :
  sin ((n + 1) * θ) = (U ℂ n).eval (cos θ) * sin θ :=
(U_complex_cos θ n).symm

end polynomial.chebyshev
