/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle, Jake Levinson
-/
import ring_theory.polynomial.hermite.basic
import analysis.calculus.deriv.pow
import analysis.calculus.deriv.add
import analysis.special_functions.exp
import analysis.special_functions.exp_deriv

/-!
# Hermite polynomials and Gaussians

This file shows that the Hermite polynomial `hermite n` is (up to sign) the
polynomial factor occurring in the `n`th derivative of a gaussian.

## Results

* `polynomial.deriv_gaussian_eq_hermite_mul_gaussian`:
  The Hermite polynomial is (up to sign) the polynomial factor occurring in the
  `n`th derivative of a gaussian.

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/

noncomputable theory
open polynomial

namespace polynomial

/-- `hermite n` is (up to sign) the factor appearing in `deriv^[n]` of a gaussian -/
lemma deriv_gaussian_eq_hermite_mul_gaussian (n : ℕ) (x : ℝ) :
  deriv^[n] (λ y, real.exp (-(y^2 / 2))) x =
  (-1 : ℝ)^n * aeval x (hermite n) * real.exp (-(x^2 / 2)) :=
begin
  rw mul_assoc,
  induction n with n ih generalizing x,
  { rw [function.iterate_zero_apply, pow_zero, one_mul, hermite_zero, C_1, map_one, one_mul] },
  { replace ih : (deriv^[n] _) = _ := _root_.funext ih,
    have deriv_gaussian : deriv (λ y, real.exp (-(y^2 / 2))) x = (-x) * real.exp (-(x^2 / 2)),
    { simp [mul_comm, ← neg_mul] },
    rw [function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_mul, pow_succ (-1 : ℝ),
        deriv_gaussian, hermite_succ, map_sub, map_mul, aeval_X, polynomial.deriv_aeval],
    ring,
    { apply polynomial.differentiable_aeval },
    { simp } }
end

lemma hermite_eq_deriv_gaussian (n : ℕ) (x : ℝ) :
  aeval x (hermite n) =
  (-1 : ℝ)^n * (deriv^[n] (λ y, real.exp (-(y^2 / 2))) x) / real.exp (-(x^2 / 2)) :=
begin
  rw deriv_gaussian_eq_hermite_mul_gaussian,
  field_simp [real.exp_ne_zero],
  rw [← @smul_eq_mul ℝ _ ((-1)^n), ← inv_smul_eq_iff₀, mul_assoc, smul_eq_mul,
      ← inv_pow, ← neg_inv, inv_one],
  exact pow_ne_zero _ (by norm_num),
end

lemma hermite_eq_deriv_gaussian' (n : ℕ) (x : ℝ) :
  aeval x (hermite n) =
  (-1 : ℝ)^n * (deriv^[n] (λ y, real.exp (-(y^2 / 2))) x) * real.exp (x^2 / 2) :=
begin
  rw [hermite_eq_deriv_gaussian, real.exp_neg],
  field_simp [real.exp_ne_zero],
end

end polynomial
