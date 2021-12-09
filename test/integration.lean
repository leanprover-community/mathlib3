/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/

import analysis.special_functions.integrals
open interval_integral real
open_locale real

/-! ### Simple functions -/

/- constants -/
example : ∫ x : ℝ in 8..11, (1 : ℝ) = 3 := by norm_num
example : ∫ x : ℝ in 5..19, (12 : ℝ) = 168 := by norm_num

/- the identity function -/
example : ∫ x : ℝ in (-1)..4, x = 15 / 2 := by norm_num
example : ∫ x : ℝ in 4..5, x * 2 = 9 := by norm_num

/- inverse -/
example : ∫ x : ℝ in 2..3, x⁻¹ = log (3 / 2) := by norm_num

/- natural powers -/
example : ∫ x : ℝ in 2..4, x ^ (3 : ℕ) = 60 := by norm_num

/- trigonometric functions -/
example : ∫ x in 0..π, sin x = 2 := by norm_num
example : ∫ x in 0..π/4, cos x = sqrt 2 / 2 := by simp
example : ∫ x in 0..π, 2 * sin x = 4 := by norm_num
example : ∫ x in 0..π/2, cos x / 2 = 1 / 2 := by simp
example : ∫ x : ℝ in 0..1, 1 / (1 + x ^ 2) = π / 4 := by simp
example : ∫ x in 0..2*π, sin x ^ 2 = π := by simp [mul_div_cancel_left]
example : ∫ x in 0..π/2, cos x ^ 2 / 2 = π / 8 := by norm_num [div_div_eq_div_mul]
example : ∫ x in 0..π, cos x ^ 2 - sin x ^ 2 = 0 := by simp [integral_cos_sq_sub_sin_sq]
example : ∫ x in 0..π/2, sin x ^ 3 = 2 / 3 := by norm_num
example : ∫ x in 0..π/2, cos x ^ 3 = 2 / 3 := by norm_num
example : ∫ x in 0..π, sin x * cos x = 0 := by simp
example : ∫ x in 0..π, sin x ^ 2 * cos x ^ 2 = π / 8 := by simpa using sin_nat_mul_pi 4

/- the exponential function -/
example : ∫ x in 0..2, -exp x = 1 - exp 2 := by simp

/- the logarithmic function -/
example : ∫ x in 1..2, log x = 2 * log 2 - 1 := by { norm_num, ring }

/- linear combinations (e.g. polynomials) -/
example : ∫ x : ℝ in 0..2, 6*x^5 + 3*x^4 + x^3 - 2*x^2 + x - 7 = 1048 / 15 := by norm_num
example : ∫ x : ℝ in 0..1, exp x + 9 * x^8 + x^3 - x/2 + (1 + x^2)⁻¹ = exp 1 + π / 4 := by norm_num

/-! ### Functions composed with multiplication by and/or addition of a constant -/

/- many examples are computable by `norm_num` -/
example : ∫ x in 0..2, -exp (-x) = exp (-2) - 1 := by norm_num
example : ∫ x in 1..2, exp (5*x - 5) = 1/5 * (exp 5 - 1) := by norm_num
example : ∫ x in 0..π, cos (x/2) = 2 := by norm_num
example : ∫ x in 0..π/4, sin (2*x) = 1/2 := by norm_num [mul_div_comm, mul_one_div]
example (ω φ : ℝ) : ω * ∫ θ in 0..π, sin (ω*θ + φ) = cos φ - cos (ω*π + φ) := by simp

/- some examples may require a bit of algebraic massaging -/
example {L : ℝ} (h : L ≠ 0) : ∫ x in 0..2/L*π, sin (L/2 * x) = 4 / L :=
begin
  norm_num [div_ne_zero h, ← mul_assoc],
  field_simp [h, mul_div_cancel],
  norm_num,
end

/- you may need to provide `norm_num` with the composition lemma you are invoking if it has a
  difficult time recognizing the function you are trying to integrate -/
example : ∫ x : ℝ in 0..2, 3 * (x + 1) ^ 2 = 26 :=
  by norm_num [integral_comp_add_right (λ x, x ^ 2)]
example : ∫ x : ℝ in -1..0, (1 + (x + 1) ^ 2)⁻¹ = π / 4 :=
  by simp [integral_comp_add_right (λ x, (1 + x ^ 2)⁻¹)]

/-! ### Compositions of functions (aka "change of variables" or "integration by substitution") -/

/- `interval_integral.integral_comp_mul_deriv` can be used to simplify integrals of the form
  `∫ x in a..b, (g ∘ f) x * f' x`, where `f'` is the derivative of `f`, to `∫ x in f a..f b, g x` -/
example {a b : ℝ} : ∫ x in a..b, exp (exp x) * exp x = ∫ x in exp a..exp b, exp x :=
integral_comp_mul_deriv (λ x hx, has_deriv_at_exp x) continuous_on_exp continuous_exp

/- if it is known (to mathlib), the integral of `g` can then be evaluated using `simp`/`norm_num` -/
example : ∫ x in 0..1, exp (exp x) * exp x = exp (exp 1) - exp 1 :=
by rw integral_comp_mul_deriv (λ x hx, has_deriv_at_exp x) continuous_on_exp continuous_exp; simp

/- a more detailed example -/
example : ∫ x in 0..2, exp (x ^ 2) * (2 * x) = exp 4 - 1 :=
begin                                                    -- let g := exp x, f := x ^ 2, f' := 2 * x
  rw integral_comp_mul_deriv (λ x hx, _),                -- simplify to ∫ x in f 0..f 2, g x
  { norm_num },                                          -- compute the integral
  { exact continuous_on_const.mul continuous_on_id },    -- show that f' is continuous on [0, 2]
  { exact continuous_exp },                              -- show that g is continuous
  { simpa using has_deriv_at_pow 2 x },                  -- show that f' = derivative of f on [0, 2]
end

/- alternatively, `interval_integral.integral_deriv_comp_mul_deriv` can be used to compute integrals
  of this same form, provided that you also know that `g` is the derivative of some function -/
example : ∫ x : ℝ in 0..1, exp (x ^ 2) * (2 * x) = exp 1 - 1 :=
begin
  rw integral_deriv_comp_mul_deriv (λ x hx, _) (λ x hx, has_deriv_at_exp (x^2)) _ continuous_exp,
  { simp },
  { simpa using has_deriv_at_pow 2 x },
  { exact continuous_on_const.mul continuous_on_id },
end
