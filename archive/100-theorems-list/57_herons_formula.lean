/-
Copyright (c) 2020 Matt Kempster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Kempster
-/
import geometry.euclidean.triangle
import analysis.special_functions.trigonometric

/-!
# Freek № 57: Heron's Formula

This file proves Theorem 57 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/),
also known as Heron's formula, which gives the area of a triangle based only on its three sides'
lengths.

## References

* https://en.wikipedia.org/wiki/Herons_formula

-/

open real
open euclidean_geometry
open_locale real euclidean_geometry

notation `√` := real.sqrt

variables {V : Type*} {P : Type*} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P]

lemma rearrange_cos_rule (a b c d : ℝ) (a_nonzero : a ≠ 0) (b_nonzero : b ≠ 0):
  c * c = a * a + b * b - 2 * a * b * d → d = (a * a + b * b - c * c) / (2 * a * b) :=
begin
  intro hyp,
  simp only [*, sub_sub_cancel],
  field_simp,
  ring,
end

include V
/-- Heron's formula: The area of a triangle with side lengths `a`, `b`, and `c` is
  `√(s * (s - a) * (s - b) * (s - c))` where `s = (a + b + c) / 2` is the semiperimeter.
  We show this by equating this formula to `a * b * sin γ`, where `γ` is the angle opposite
  the side `c`.
 -/
theorem heron {p1 p2 p3 : P} (h1 : p1 ≠ p2) (h2 : p3 ≠ p2) :
  let a := dist p1 p2, b := dist p3 p2, c := dist p1 p3, s := (a + b + c) / 2 in
  1/2 * a * b * real.sin (∠ p1 p2 p3) = √(s * (s - a) * (s - b) * (s - c)) :=
begin
  intros a b c s,
  let γ := ∠ p1 p2 p3,

  have a_nonzero : a ≠ 0 := (dist_pos.mpr h1).ne',
  have b_nonzero : b ≠ 0 := (dist_pos.mpr h2).ne',

  have cos_rule := rearrange_cos_rule a b c (real.cos γ) a_nonzero b_nonzero
    (dist_square_eq_dist_square_add_dist_square_sub_two_mul_dist_mul_dist_mul_cos_angle p1 p2 p3),

  have sin_to_cos := sin_eq_sqrt_one_minus_cos_sq γ (angle_nonneg p1 p2 p3) (angle_le_pi p1 p2 p3),

  let numerator := (2*a*b)^2 - (a*a + b*b - c*c)^2,
  let denominator := (2*a*b)^2,

  have split_to_fraction :=
  calc    1 - real.cos γ ^ 2
        = 1 - ((a*a + b*b - c*c) / (2*a*b))^2           : by rw cos_rule
    ... = 1 - (a*a + b*b - c*c)^2 / (2*a*b)^2           : by { congr', exact div_pow _ (2*a*b) 2 }
    ... = ((2*a*b)^2 - (a*a + b*b - c*c)^2) / (2*a*b)^2 : by field_simp
    ... = numerator / denominator                       : rfl,

  have ab2_pos : 0 ≤ (2 * a * b), by { field_simp *, linarith },

  have numerator_nonneg : 0 ≤ numerator, by
  { have denom_nonneg : 0 ≤ (2*a*b)^2, by { rw pow_two, exact mul_nonneg ab2_pos ab2_pos },
    have frac_nonneg: 0 ≤ numerator / denominator,
      by { rw ← split_to_fraction, linarith [real.cos_sq_le_one γ] },
    rw div_nonneg_iff at frac_nonneg,
    cases frac_nonneg,
    { exact frac_nonneg.left },
    { exfalso,
      have ab2_sqr_zero : (2*a*b)*(2*a*b) = 0,
        by { rw ← pow_two, exact le_antisymm frac_nonneg.right denom_nonneg },
      field_simp at ab2_sqr_zero,
      exact ab2_sqr_zero } },

  set s := (a + b + c) / 2 with hs,

  calc    1/2*a*b * real.sin γ
        = 1/2*a*b * √(1 - real.cos γ ^ 2)           : by rw sin_to_cos
    ... = 1/2*a*b * √(numerator / denominator)      : by rw ← split_to_fraction
    ... = 1/2*a*b * √(numerator) / √(denominator)   : by { rw real.sqrt_div numerator_nonneg, ring }
    ... = 1/2*a*b * √((2*a*b)^2 - (a*a + b*b - c*c)^2) / √((2*a*b)^2) : rfl
    ... = 1/4 * √((2*a*b)^2 - (a*a + b*b - c*c)^2)  : by { field_simp [ab2_pos], ring }
    ... = 1/4 * √(s * (s-a) * (s-b) * (s-c) * 4^2)  : by { rw hs, ring_nf }
    ... = √(s * (s-a) * (s-b) * (s-c))              : by
      rw [real.sqrt_mul', real.sqrt_sqr, div_mul_eq_mul_div, one_mul, mul_div_cancel]; norm_num,
end
