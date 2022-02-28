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
  rw [sub_add],
  apply lt_of_lt_of_le _ (sub_zero x).le,
  apply sub_lt_sub_left,
  rw [sub_pos, div_eq_mul_inv (x ^ 3)],
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
  rw [add_comm, sub_add, sub_neg_eq_add],
  apply sub_lt_sub_left,
  apply add_lt_of_lt_sub_left,
  have : x ^ 3 / 4 - x ^ 3 / 6 = x ^ 3 * 12⁻¹ := by norm_num [div_eq_mul_inv, ← mul_sub],
  rw this,
  refine mul_lt_mul' _ (by norm_num) (by norm_num) (pow_pos h 3),
  apply pow_le_pow_of_le_one h.le h',
  norm_num
end


/- The next lemmas are building up to proving tan(x) > x for x ∈ (0,π/2). -/

private def tan_minus_id (x : ℝ) : ℝ := tan x - x

private def tansq (x : ℝ) (h : cos x ≠ 0) : ℝ := 1/(cos x)^2 - 1

private lemma tan_minus_id_deriv (x : ℝ) (h: cos x ≠ 0) :
    deriv tan_minus_id x = (tansq x h) :=
begin
  apply has_deriv_at.deriv,
  simp only [tansq],
  have uv := has_deriv_at.add (has_deriv_at_tan h) (has_deriv_at.neg (has_deriv_at_id x)),
  simp at *,
  exact uv,
end

/- tansq is positive away from the obvious bad points -/
private lemma tansq_pos (x : ℝ) (h : cos x ≠ 0) (h2: sin x ≠ 0):
  tansq x h > 0 :=
begin
  simp only [tansq, one_div, gt_iff_lt, sub_pos],
  have bd2 : cos x ^2 < 1,
  { apply lt_of_le_of_ne x.cos_sq_le_one,
    rw cos_sq',
    simp only [ne.def, sub_eq_self, pow_eq_zero_iff, nat.succ_pos'],
    exact h2 },
  rw [lt_inv,inv_one],
  exact bd2,
  apply zero_lt_one,
  rwa [sq,mul_self_pos],
end

/- cos is nonzero on the Ico interval -/
private lemma cos_nz (x : ℝ) (h1: 0 ≤ x) (h2: x < π/2): cos x ≠ 0 :=
begin
  intro coszero,
  have : (x ∈ (Ioo (-(π / 2 : ℝ)) (π / 2 : ℝ))),
  { split,
    apply (lt_of_lt_of_le _ h1),
    rw [neg_lt,neg_zero],
    exact pi_div_two_pos,
    exact h2 },
  have s : (cos x > 0) := cos_pos_of_mem_Ioo this,
  rw coszero at s,
  exact (gt_irrefl (0:ℝ)) s,
end

/- sin is nonzero on the Ioo interval -/
private lemma sin_nz (x: ℝ) (h1: 0 < x) (h2: x < π/2) : sin x ≠ 0 :=
begin
  apply ne_of_gt,
  apply sin_pos_of_pos_of_lt_pi h1,
  apply lt_trans h2,
  rw ← lt_add_neg_iff_lt,
  have : π + -(π / 2) = π/2 := by ring,
  rw this, exact pi_div_two_pos,
end

private def U := Ico 0 (π/2 : ℝ)

/-- For all `0 ≤ x < π/2` we have `x < tan x`.

This is proved by checking that the function `tan x - x` vanishes
at zero and has non-negative derivative. -/
theorem lt_tan (x : ℝ) (h1: (0:ℝ) < x) (h2: x < π/2): x < tan x :=
begin
  have intU : (interior U) = (Ioo (0:ℝ) (π/2:ℝ)) := by apply interior_Ico,
  have tan_cts_U : (continuous_on tan U),
  { apply continuous_on.mono continuous_on_tan,
    intros z hz,
    rw [U, Ico] at hz,
    simp only [ne.def, mem_set_of_eq] at *,
    cases hz with zlo zhi,
    exact cos_nz z zlo zhi },

  have tan_minus_id_cts : (continuous_on tan_minus_id U),
  { have : continuous_on (id: ℝ → ℝ) U := continuous_on_id,
    exact continuous_on.sub tan_cts_U this},

  have deriv_pos : (∀ (y : ℝ), y ∈ interior U → 0 < deriv tan_minus_id y),
  { intros y hy,
    have t := interior_subset hy,
    rw [intU,Ioo] at hy,
    cases hy with ylo yhi,
    rw tan_minus_id_deriv,
    apply tansq_pos,
    apply sin_nz y ylo yhi,
    apply cos_nz y (le_of_lt ylo) yhi },

  have mon:= (convex.strict_mono_on_of_deriv_pos
    (convex_Ico 0 (π/2 : ℝ)) tan_minus_id_cts deriv_pos),

  have zero_in_U: (0:ℝ) ∈ U,
  { rw [U, Ico],
    simp only [mem_set_of_eq, le_refl, true_and],
    exact pi_div_two_pos },
  have x_in_U : (x ∈ U),
  { rw [U,Ico],
    simp only [mem_set_of_eq],
    split,
    exact le_of_lt h1, exact h2 },
  have w := mon zero_in_U x_in_U h1,
  rwa [tan_minus_id,tan_zero,
    sub_zero,tan_minus_id,
    lt_sub,sub_zero, ←gt_iff_lt] at w,
end

end real
