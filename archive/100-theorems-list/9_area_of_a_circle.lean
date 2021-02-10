/-
Copyright (c) 2021 James Arthur, Benjamin Davidson, Andrew Souther. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Benjamin Davidson, Andrew Souther
-/
import measure_theory.interval_integral
import analysis.special_functions.trigonometric
import analysis.mean_inequalities

/-!
# Freek № 9: The Area of a Circle

In this file we show that the area of a disc with radius `r` (with `0 < r`) is `π * r^2`. The main
tools our proof uses are `volume_region_between_eq_integral`, which allows us to represent the area
of the disc as an integral, and `interval_integral.integral_eq_sub_of_has_deriv_at'_of_le`, the
second fundamental theorem of calculus.

We begin by defining `disc` in `ℝ × ℝ`, then show that `disc` can be represented as the
`region_between` two functions.

Though not necessary for the main proof, we nonetheless choose to include a proof of the
measurability of the disc in order to convince the reader that the set whose volume we will be
calculating is indeed measurable and our result is therefore meaningful.

In the main proof, `area_disc`, we use `volume_region_between_eq_integral` followed by
`interval_integral.integral_of_le` to reduce our goal to a single `interval_integral`:
  `∫ (x : ℝ) in -r..r, 2 * sqrt (r ^ 2 - x ^ 2) = π * r ^ 2`.
After showing that `λ x, 2 * sqrt (r ^ 2 - x ^ 2)` is equal to the derivative of
`λ x, r ^ 2 * arcsin (x / r) + x * sqrt (r ^ 2 - x ^ 2)` everywhere on `Ioo (-r) r` (and that those
two functions are continuous), we apply `interval_integral.integral_eq_sub_of_has_deriv_at'_of_le`.
Some simple algebra then completes the proof.

Note that we choose to define `disc` as a set of points in `ℝ ⨯ ℝ`. This is admittedly not ideal; it
would be more natural to define `disc` as a `metric.ball` in `fin 2 → ℝ` (as well as to provide a
more general proof in higher dimensions). However, our proof indirectly relies on a number of
theorems (particularly `measure_theory.prod.prod_apply`) which do not yet exist for Euclidean space,
thus forcing us to use this less-preferable definition. As `measure_theory.pi` continues to develop,
it should eventually become possible to redefine `disc` and extend our proof to the n-ball.
-/

open set real filter measure_theory interval_integral
variable {r : ℝ}

/-- A disc of radius `r` is defined as the collection of points `(p.1, p.2)` in `ℝ × ℝ` such that
  `p.1 ^ 2 + p.2 ^ 2 < r ^ 2`. -/
def disc (h : 0 < r) := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}

/-- A disc of radius `r` can be represented as the region between the two curves
  `λ x, - sqrt (r ^ 2 - x ^ 2)` and `λ x, sqrt (r ^ 2 - x ^ 2)`. -/
lemma disc_eq_region_between {hr : 0 < r} :
  disc hr = region_between (λ x, -sqrt (r^2 - x^2)) (λ x, sqrt (r^2 - x^2)) (Ioc (-r) r) :=
begin
  ext p,
  simp only [disc, region_between, mem_set_of_eq, mem_Ioo, mem_Ioc, pi.neg_apply],
  split;
  intro h,
  { split,
    { rw ← sqrt_sqr hr.le,
      have h' : p.1^2 < r^2 := by linarith [pow_two_nonneg p.2],
      exact ⟨neg_sqrt_lt_of_sqr_lt h', (lt_sqrt_of_sqr_lt h').le⟩ },
    { rw [add_comm, ← lt_sub_iff_add_lt] at h,
      exact sqr_lt.mp h } },
  { rw [add_comm, ← lt_sub_iff_add_lt],
    exact sqr_lt.mpr h.2 },
end

/-- For convenience we show a fact we will need multiple times throughout the following proofs:
  For any real `a`, `λ x, sqrt (a - x ^ 2)` is a continuous function. -/
lemma continuous_sqrt_sub {a : ℝ} : continuous (λ x, sqrt (a - x ^ 2)) :=
(continuous_const.sub (continuous_pow 2)).sqrt

alias continuous_sqrt_sub ← hc

/-- The disc is a `measurable_set`. -/
theorem measurable_set_disc (hr : 0 < r) : measurable_set (disc hr) :=
begin
  rw disc_eq_region_between,
  exact measurable_set_region_between hc.neg.measurable hc.measurable measurable_set_Ioc,
end

/-- The area of a disc with radius `r` is `π * r ^ 2`. -/
theorem area_disc (hr : 0 < r) : volume (disc hr) = ennreal.of_real (pi * r ^ 2) :=
begin
  let f := λ x, sqrt (r ^ 2 - x ^ 2),
  let F := λ x, r ^ 2 * arcsin (r⁻¹ * x) + x * sqrt (r ^ 2 - x ^ 2),
  suffices : ∫ x in Ioc (-r) r, (f - has_neg.neg ∘ f) x = pi * r ^ 2,
  { have H : ∀ {g : ℝ → ℝ}, continuous g → integrable_on g (Ioc (-r) r) :=
      λ g hg, (hg.integrable_on_compact compact_Icc).mono_set Ioc_subset_Icc_self,
    erw [disc_eq_region_between, ← this,
        volume_region_between_eq_integral (H hc.neg) (H hc) measurable_set_Ioc
          (λ x hx, neg_le_self (sqrt_nonneg _))] },
  have hderiv : ∀ x ∈ Ioo (-r) r, has_deriv_at F (2 * f x) x,
  { rintros x ⟨hx1, hx2⟩,
    convert ((has_deriv_at_const x (r^2)).mul ((has_deriv_at_arcsin _ _).comp x
      ((has_deriv_at_const x r⁻¹).mul (has_deriv_at_id' x)))).add
        ((has_deriv_at_id' x).mul (((has_deriv_at_id' x).pow.const_sub (r^2)).sqrt _)),
    { have h : sqrt (1 - x ^ 2 / r ^ 2) * r = sqrt (r ^ 2 - x ^ 2),
      { rw [← sqrt_sqr hr.le, ← sqrt_mul, sub_mul, sqrt_sqr hr.le, div_mul_eq_mul_div_comm,
            div_self (pow_ne_zero 2 hr.ne'), one_mul, mul_one],
        simpa only [sub_nonneg, sqrt_sqr hr.le, div_le_one (pow_pos hr 2)]
          using (sqr_lt_sqr' hx1 hx2).le },
      field_simp,
      rw [h, mul_left_comm, ← pow_two, neg_mul_eq_mul_neg, mul_div_mul_left (-x^2) _ two_ne_zero,
          add_left_comm, div_add_div_same, tactic.ring.add_neg_eq_sub, div_sqrt, two_mul] },
    { by_contra hnot,
      rw [not_not, eq_neg_iff_eq_neg, ← one_div, div_mul_eq_mul_div, one_mul,
          ← div_neg_eq_neg_div, eq_comm, div_eq_one_iff_eq (neg_ne_zero.mpr hr.ne')] at hnot,
      exact hx1.ne' hnot },
    { by_contra hnot,
      rw [not_not, ← one_div, div_mul_eq_mul_div, one_mul, div_eq_one_iff_eq hr.ne'] at hnot,
      exact hx2.ne hnot },
    { simpa only [sub_ne_zero] using (sqr_lt_sqr' hx1 hx2).ne' } },
  have Fcont := ((continuous_const.mul (continuous_arcsin.comp
                  ((@continuous_const _ _ _ _ r⁻¹).mul continuous_id))).add
                    (continuous_id.mul (@hc (r^2)))).continuous_on,
  have fcont := (continuous_const.mul hc).continuous_on,
  calc  ∫ x in Ioc (-r) r, (f - has_neg.neg ∘ f) x
      = ∫ x in Ioc (-r) r, (λ x, 2 * f x) x : by simp only [pi.sub_apply, sub_neg_eq_add, ← two_mul]
  ... = ∫ x in (-r)..r, (λ x, 2 * f x) x : (integral_of_le (neg_le_self hr.le)).symm
  ... = F r - F (-r) : integral_eq_sub_of_has_deriv_at'_of_le (neg_le_self hr.le) Fcont hderiv fcont
  ... = pi * r ^ 2 : by simp_rw [F, ← neg_mul_eq_mul_neg, inv_mul_cancel hr.ne', arcsin_neg,
                                arcsin_one, neg_square, sub_self, sqrt_zero, mul_zero, add_zero,
                                ← neg_mul_eq_mul_neg, sub_neg_eq_add, ← mul_div_assoc, add_halves',
                                mul_comm],
end

theorem area_disc' (hr : 0 < r) : volume (disc hr) = ennreal.of_real (pi * r ^ 2) :=
begin
  have H : ∀ {f : ℝ → ℝ}, continuous f → integrable_on f (Ioc (-r) r) :=
    λ f h, (h.integrable_on_compact compact_Icc).mono_set Ioc_subset_Icc_self,
  rw disc_eq_region_between,
  convert volume_region_between_eq_integral (H hc.neg) (H hc) measurable_set_Ioc
    (λ x hx, neg_le_self (sqrt_nonneg _)),
  simp only [pi.sub_apply, sub_neg_eq_add, ← two_mul, ← integral_of_le (neg_le_self hr.le)],
  rw integral_eq_sub_of_has_deriv_at'_of_le (neg_le_self hr.le) ((continuous_const.mul
      (continuous_arcsin.comp (continuous_id.div continuous_const (λ x, hr.ne')))).add
        (continuous_id.mul (@hc (r^2)))).continuous_on _ (continuous_const.mul hc).continuous_on,
  { simp_rw [function.comp_app, pi.div_apply, id.def, neg_div, div_self hr.ne', arcsin_neg,
            arcsin_one, neg_square, sub_self, sqrt_zero, mul_zero, add_zero,
            mul_neg_eq_neg_mul_symm, sub_neg_eq_add, ← mul_div_assoc, add_halves', mul_comm] },
  { rintros x ⟨hx1, hx2⟩,
    convert ((has_deriv_at_const x (r^2)).mul ((has_deriv_at_arcsin _ _).comp x
      ((has_deriv_at_id' x).div (has_deriv_at_const x r) hr.ne'))).add
        ((has_deriv_at_id' x).mul (((has_deriv_at_id' x).pow.const_sub (r^2)).sqrt _)),
    { have h : sqrt (1 - x ^ 2 / r ^ 2) * r ^ 2 = r * sqrt (r ^ 2 - x ^ 2),
      { rw [← sqrt_sqr (pow_two_nonneg r), ← sqrt_mul, sub_mul, sqrt_sqr (pow_two_nonneg r),
            div_mul_eq_mul_div_comm, pow_two, mul_div_cancel_left _ (pow_ne_zero 2 hr.ne'),
            ← mul_assoc, ← sub_mul, mul_comm, sqrt_mul (pow_two_nonneg r), sqrt_sqr hr.le, one_mul],
        simpa only [sub_nonneg, sqrt_sqr (pow_two_nonneg r), div_le_one (pow_pos hr 2)]
          using (sqr_lt_sqr' hx1 hx2).le },
      field_simp,
      rw [h, mul_div_assoc, ← div_div_eq_div_mul, div_self hr.ne', mul_one_div, mul_left_comm,
          ← pow_two, neg_div, mul_div_mul_left (x^2) (sqrt (r^2-x^2)) two_ne_zero, ← add_assoc,
          add_right_comm, tactic.ring.add_neg_eq_sub, div_sub_div_same, div_sqrt, two_mul] },
    { by_contra hnot,
      rw [not_not, eq_neg_iff_eq_neg, ← div_neg, eq_comm,
          div_eq_one_iff_eq (neg_ne_zero.mpr hr.ne')] at hnot,
      exact hx1.ne' hnot },
    { by_contra hnot,
      rw [not_not, div_eq_one_iff_eq hr.ne'] at hnot,
      exact hx2.ne hnot },
    { simpa only [sub_ne_zero] using (sqr_lt_sqr' hx1 hx2).ne' } },
end
