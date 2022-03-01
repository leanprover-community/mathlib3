/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import analysis.special_functions.trigonometric.basic
import analysis.special_functions.trigonometric.deriv
import analysis.special_functions.trigonometric.arctan_deriv
/-!
# Polynomial bounds for trigonometric functions

## Main statements

This file contains upper and lower bounds for real trigonometric functions in terms
of polynomials. See `trigonometric.basic` for more elementary inequalities, establishing
the ranges of these functions, and their monotonicity in suitable intervals.

Here we prove the following:

* `sin_lt`: for `x > 0` we have `sin x < x`.
* `sin_gt_sub_cube`: For `0 < x ≤ 1` we have `x - x ^ 3 / 4 < sin x`.
* `lt_tan`: for `0 < x < π/2` we have `x < tan x`.

## Tags

sin, cos, tan, angle
-/

noncomputable theory
open set

namespace real
open_locale real

/-- For 0 < x, we have sin x < x. -/
lemma sin_lt {x : ℝ} (h : 0 < x) : sin x < x :=
begin
  cases lt_or_ge 1 x with h' h',
  { exact (sin_le_one x).trans_lt h' },
  have hx : |x| = x := abs_of_nonneg h.le,
  have := le_of_abs_le (sin_bound $ show |x| ≤ 1, by rwa [hx]),
  rw [sub_le_iff_le_add', hx] at this,
  apply this.trans_lt,
  rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)],
  refine mul_lt_mul' _ (by norm_num) (by norm_num) (pow_pos h 3),
  apply pow_le_pow_of_le_one h.le h',
  norm_num
end

/-- For 0 < x ≤ 1 we have x - x ^ 3 / 4 < sin x.

This is also true for x > 1, but it's nontrivial for x just above 1. This inequality is not
tight; the tighter inequality is sin x > x - x ^ 3 / 6 for all x > 0, but this inequality has
a simpler proof. -/
lemma sin_gt_sub_cube {x : ℝ} (h : 0 < x) (h' : x ≤ 1) : x - x ^ 3 / 4 < sin x :=
begin
  have hx : |x| = x := abs_of_nonneg h.le,
  have := neg_le_of_abs_le (sin_bound $ show |x| ≤ 1, by rwa [hx]),
  rw [le_sub_iff_add_le, hx] at this,
  refine lt_of_lt_of_le _ this,
  have : x ^ 3 / 4 - x ^ 3 / 6 = x ^ 3 * 12⁻¹ := by norm_num [div_eq_mul_inv, ← mul_sub],
  rw [add_comm, sub_add, sub_neg_eq_add, sub_lt_sub_iff_left, ←lt_sub_iff_add_lt', this],
  refine mul_lt_mul' _ (by norm_num) (by norm_num) (pow_pos h 3),
  apply pow_le_pow_of_le_one h.le h',
  norm_num
end


/-- The derivative of `tan x - x` is `1/(cos x)^2 - 1` away from the zeroes of cos. -/
lemma deriv_tan_sub_id (x : ℝ) (h: cos x ≠ 0) :
    deriv (λ y : ℝ, tan y - y) x = 1 / cos x ^ 2 - 1 :=
has_deriv_at.deriv $ by simpa using (has_deriv_at_tan h).add (has_deriv_at_id x).neg

private def U := Ico 0 (π/2)

/-- For all `0 ≤ x < π/2` we have `x < tan x`.

This is proved by checking that the function `tan x - x` vanishes
at zero and has non-negative derivative. -/
theorem lt_tan (x : ℝ) (h1 : 0 < x) (h2 : x < π / 2): x < tan x :=
begin
  have intU : interior U = Ioo 0 (π/2) := interior_Ico,

  have cos_pos : ∀ y : ℝ, (0 ≤ y) → (y < π/2) → (0 < cos y),
  { intros y y1 y2,
    apply cos_pos_of_mem_Ioo,
    split; linarith, },

  have sin_pos : ∀ y : ℝ, 0 < y → y < π / 2 → 0 < sin y,
  { intros y hy1 hy2,
    apply sin_pos_of_pos_of_lt_pi hy1,
    apply lt_trans hy2,
    rw ← lt_add_neg_iff_lt,
    have : π + -(π / 2) = π/2 := by ring,
    rw this, exact pi_div_two_pos },

  have tan_cts_U : continuous_on tan U,
  { apply continuous_on.mono continuous_on_tan,
    intros z hz,
    rw [U, Ico] at hz,
    simp only [ne.def, mem_set_of_eq] at *,
    exact (cos_pos z hz.1 hz.2).ne' },

  have tan_minus_id_cts : continuous_on (λ y : ℝ, tan y - y) U :=
    tan_cts_U.sub continuous_on_id,

  have deriv_pos : ∀ y : ℝ, y ∈ interior U → 0 < deriv (λ y' : ℝ, tan y' - y') y,
  { intros y hy,
    rw [intU, Ioo] at hy,
    have := (cos_pos y (le_of_lt hy.1) hy.2).ne',
    simp only [deriv_tan_sub_id y this, one_div, gt_iff_lt, sub_pos],
    have bd2 : cos y ^ 2 < 1,
    { apply lt_of_le_of_ne y.cos_sq_le_one,
      rw cos_sq',
      simpa only [ne.def, sub_eq_self, pow_eq_zero_iff, nat.succ_pos']
        using (sin_pos y hy.left hy.right).ne' },
    rwa [lt_inv, inv_one],
    { exact zero_lt_one },
    { rwa [sq, mul_self_pos] } },
  have mono := convex.strict_mono_on_of_deriv_pos (convex_Ico 0 (π / 2)) tan_minus_id_cts deriv_pos,
  have zero_in_U : (0 : ℝ) ∈ U,
  { split; linarith },
  have x_in_U : x ∈ U,
  { split; linarith },
  simpa only [tan_zero, sub_zero, sub_pos] using mono zero_in_U x_in_U h1,
end

end real
