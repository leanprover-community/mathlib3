/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle, Jake Levinson
-/

import ring_theory.polynomial.hermite.basic
import analysis.special_functions.exp
import analysis.special_functions.exp_deriv

/-!
# Hermite polynomials and Gaussians

This file shows that the Hermite polynomial `hermite n` is (up to sign) the
polynomial factor occurring in the `n`th derivative of a gaussian.

## Results

* `polynomial.hermite_eq_deriv_gaussian`: the Hermite polynomial is (up to sign) the polynomial
factor occurring in the `n`th derivative of a gaussian.

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/

noncomputable theory
open polynomial

namespace polynomial

/- `hermite n` is (up to sign) the factor appearing in `deriv^[n]` of a gaussian -/
lemma hermite_eq_deriv_gaussian (n : ℕ) (x : ℝ) :
  aeval x (hermite n) =
  (-1 : ℝ)^n * (deriv^[n] (λ y, real.exp (-(y^2 / 2))) x) / real.exp (-(x^2 / 2)) :=
begin
  induction n with n ih generalizing x,
  { simp [← real.exp_sub] },
  { let gaussian : ℝ → ℝ := λ x, real.exp (-(x^2 / 2)),
    have gaussian_ne_zero : ∀ x, gaussian x ≠ 0 := by simp [gaussian, real.exp_ne_zero],
    have cont_diff_gaussian : cont_diff ℝ ⊤ gaussian := ((cont_diff_id.pow 2).div_const 2).neg.exp,
    have : ∀ x n,
      (-1 : ℝ)^(n+1) * (deriv^[n+1] gaussian x) / gaussian x
      = x * ((-1 : ℝ)^n * (deriv^[n] gaussian x) / gaussian x) -
        deriv (λ z, (-1 : ℝ)^n * (deriv^[n] gaussian z) / gaussian z) x,
    { intros x n,
      rw [function.iterate_succ_apply', deriv_div _ _ (gaussian_ne_zero _), deriv_const_mul,
          (by simp [gaussian, mul_comm] : deriv gaussian x = (-x) * gaussian x)],
      field_simp [gaussian_ne_zero],
      ring_exp,
      { apply (cont_diff_top_iff_deriv.mp (cont_diff_gaussian.iterate_deriv _)).1, },
      { apply (cont_diff_top_iff_deriv.mp _).1,
        exact (cont_diff_gaussian.iterate_deriv _).const_smul ((-1 : ℝ)^n) },
      { simp } },
    simp_rw [this, hermite_succ, ← ih, polynomial.deriv_aeval, map_sub, map_mul, aeval_X] }
end

end polynomial
