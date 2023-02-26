/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import analysis.complex.basic
import data.complex.exponential
import data.polynomial.algebra_map
import ring_theory.polynomial.chebyshev

/-!
# Multiple angle formulas in terms of Chebyshev polynomials

This file gives the trigonometric characterizations of Chebyshev polynomials, for both the real
(`real.cos`) and complex (`complex.cos`) cosine.
-/

namespace polynomial.chebyshev
open polynomial

variables {R A : Type*} [comm_ring R] [comm_ring A] [algebra R A]

@[simp] lemma aeval_T (x : A) (n : ℕ) : aeval x (T R n) = (T A n).eval x :=
by rw [aeval_def, eval₂_eq_eval_map, map_T]

@[simp] lemma aeval_U (x : A) (n : ℕ) : aeval x (U R n) = (U A n).eval x :=
by rw [aeval_def, eval₂_eq_eval_map, map_U]

@[simp] lemma algebra_map_eval_T (x : R) (n : ℕ) :
  algebra_map R A ((T R n).eval x) = (T A n).eval (algebra_map R A x) :=
by rw [←aeval_algebra_map_apply_eq_algebra_map_eval, aeval_T]

@[simp] lemma algebra_map_eval_U (x : R) (n : ℕ) :
  algebra_map R A ((U R n).eval x) = (U A n).eval (algebra_map R A x) :=
by rw [←aeval_algebra_map_apply_eq_algebra_map_eval, aeval_U]

@[simp, norm_cast] lemma complex_of_real_eval_T : ∀ x n, ((T ℝ n).eval x : ℂ) = (T ℂ n).eval x :=
@algebra_map_eval_T ℝ ℂ _ _ _

@[simp, norm_cast] lemma complex_of_real_eval_U : ∀ x n, ((U ℝ n).eval x : ℂ) = (U ℂ n).eval x :=
@algebra_map_eval_U ℝ ℂ _ _ _

/-! ### Complex versions -/

section complex
open complex

variable (θ : ℂ)

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
@[simp] lemma T_complex_cos : ∀ n, (T ℂ n).eval (cos θ) = cos (n * θ)
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

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`. -/
@[simp] lemma U_complex_cos (n : ℕ) : (U ℂ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) :=
begin
  induction n with d hd,
  { simp only [U_zero, nat.cast_zero, eval_one, mul_one, zero_add, one_mul] },
  { rw U_eq_X_mul_U_add_T,
    simp only [eval_add, eval_mul, eval_X, T_complex_cos, add_mul, mul_assoc, hd, one_mul],
    conv_rhs { rw [sin_add, mul_comm] },
    push_cast,
    simp only [add_mul, one_mul] }
end

end complex

/- ### Real versions -/

section real
open real

variables (θ : ℝ) (n : ℕ)

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
@[simp] lemma T_real_cos : (T ℝ n).eval (cos θ) = cos (n * θ) :=
by exact_mod_cast T_complex_cos θ n

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`. -/
@[simp] lemma U_real_cos : (U ℝ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) :=
by exact_mod_cast U_complex_cos θ n

end real

end polynomial.chebyshev
