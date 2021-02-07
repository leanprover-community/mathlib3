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

The area of a disc with radius `r` is `π * r^2`.
-/

open set real filter measure_theory interval_integral

/-- A disc of radius `r` is defined as the collection of points `(p.1, p.2)` in `ℝ × ℝ` such that
  `p.1 ^ 2 + p.2 ^ 2 < r ^ 2`. -/
def disc {r : ℝ} (h : 0 < r) := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}

/-- A disc of radius `r` can be represented as the region between the two curves
  `λ x, - sqrt (r ^ 2 - x ^ 2)` and `λ x, sqrt (r ^ 2 - x ^ 2)`. -/
lemma disc_eq_region_between {r : ℝ} {hr : 0 < r} :
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
  For any real `r`, `λ x, sqrt (r ^ 2 - x ^ 2)` is a continuous function. -/
lemma hc {r : ℝ} : continuous (λ x, sqrt (r ^ 2 - x ^ 2)) :=
(continuous_const.sub (continuous_pow 2)).sqrt

/-- The disc is a measurable set. Though not necessary for our proof, we choose to show this fact
  nonetheless in order to convince the reader that the set whose volume we will be calculating is
  indeed measurable and our result is therefore meaningful. -/
theorem measurable_set_disc {r : ℝ} (hr : 0 < r) : measurable_set (disc hr) :=
begin
  rw disc_eq_region_between,
  exact measurable_set_region_between hc.neg.measurable hc.measurable measurable_set_Ioc,
end

/-- The area of a disc with radius `r` is `π * r ^ 2`. -/
theorem volume_disc {r : ℝ} (hr : 0 < r) :
  volume.prod volume (disc hr) = ennreal.of_real (pi * r ^ 2) :=
begin
  have H : ∀ {f : ℝ → ℝ}, continuous f → integrable_on f (Ioc (-r) r) :=
    λ f h, (h.integrable_on_compact compact_Icc).mono_set Ioc_subset_Icc_self,
  rw disc_eq_region_between,
  convert volume_region_between_eq_integral (H hc.neg) (H hc) measurable_set_Ioc
    (λ x hx, neg_le_self (sqrt_nonneg _)),
  simp only [pi.sub_apply, sub_neg_eq_add, ← two_mul, ← integral_of_le (neg_le_self hr.le)],
  rw integral_eq_sub_of_has_deriv_at'_of_le (neg_le_self hr.le) ((continuous_const.mul
      (continuous_arcsin.comp (continuous_id.div continuous_const (λ x, hr.ne')))).add
        (continuous_id.mul (@hc r))).continuous_on _ (continuous_const.mul hc).continuous_on,
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
