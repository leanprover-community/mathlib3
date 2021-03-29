/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/

import analysis.special_functions.integrals
open interval_integral real
open_locale real

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
