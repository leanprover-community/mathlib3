/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/

import analysis.special_functions.integrals
open interval_integral real
open_locale real

/-! ### Simple functions -/

/-- constants -/
example : ∫ x : ℝ in 8..11, (1 : ℝ) = 3 := by norm_num
example : ∫ x : ℝ in 5..19, (12 : ℝ) = 168 := by norm_num

/-- the identity function -/
example : ∫ x : ℝ in (-1)..4, x = 15 / 2 := by norm_num
example : ∫ x : ℝ in 4..5, x * 2 = 9 := by norm_num

/-- inverse -/
example : ∫ x : ℝ in 2..3, x⁻¹ = log (3 / 2) := by norm_num

/-- natural powers -/
example : ∫ x : ℝ in 2..4, x ^ (3 : ℕ) = 60 := by norm_num

/-- trigonometric functions -/
example : ∫ x in 0..π, sin x = 2 := by norm_num
example : ∫ x in 0..π/4, cos x = sqrt 2 / 2 := by simp
example : ∫ x in 0..π, 2 * sin x = 4 := by norm_num
example : ∫ x in 0..π/2, cos x / 2 = 1 / 2 := by simp
example : ∫ x : ℝ in 0..1, 1 / (1 + x ^ 2) = π/4 := by simp

/-- the exponential function -/
example : ∫ x in 0..2, -exp x = 1 - exp 2 := by simp

/-- linear combinations (e.g. polynomials) -/
example : ∫ x : ℝ in 0..2, 6*x^5 + 3*x^4 + x^3 - 2*x^2 + x - 7 = 1048 / 15 := by norm_num
example : ∫ x : ℝ in 0..1, exp x + 9 * x^8 + x^3 - x/2 + (1 + x^2)⁻¹ = exp 1 + π / 4 := by norm_num

/-! ### Functions composed with multiplication by and/or addition of a constant -/

/-- many examples are computable by `norm_num` -/
example : ∫ x in 0..2, -exp (-x) = exp (-2) - 1 := by norm_num
example : ∫ x in 1..2, exp (5*x - 5) = 1/5 * (exp 5 - 1) := by norm_num
example : ∫ x in 0..π, cos (x/2) = 2 := by norm_num
example : ∫ x in 0..π/4, sin (2*x) = 1/2 := by norm_num [mul_div_comm, mul_one_div]
example {ω φ : ℝ} (h : ω ≠ 0) : ∫ θ in 0..2*π, sin (ω*θ + φ) = ω⁻¹ * (cos φ - cos (2*π*ω + φ)) :=
  by simp [h, mul_comm]

/-- some examples may require a bit of algebraic massaging -/
example {L : ℝ} (h : L ≠ 0) : ∫ x in 0..2/L*π, sin (L/2 * x) = 4 / L :=
begin
  norm_num [div_ne_zero h, ← mul_assoc],
  field_simp [h, mul_div_cancel],
  norm_num,
end

/-- you may need to provide `norm_num` with the composition lemma you are invoking if it has a
  difficult time recognizing the function you are trying to integrate -/
example : ∫ x : ℝ in 0..2, 3 * (x + 1) ^ 2 = 26 :=
  by norm_num [integral_comp_add_right (λ x, x ^ 2)]
example : ∫ x : ℝ in -1..0, (1 + (x + 1) ^ 2)⁻¹ = π/4 :=
  by simp [integral_comp_add_right (λ x, (1 + x ^ 2)⁻¹)]
