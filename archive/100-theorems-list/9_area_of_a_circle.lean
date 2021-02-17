/-
Copyright (c) 2021 James Arthur, Benjamin Davidson, Andrew Souther. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Benjamin Davidson, Andrew Souther
-/
import measure_theory.interval_integral
import analysis.special_functions.pow

/-!
# Freek № 9: The Area of a Circle

In this file we show that the area of a disc with nonnegative radius `r` is `π * r^2`. The main
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
After disposing of the trivial case `r = 0`, we show that `λ x, 2 * sqrt (r ^ 2 - x ^ 2)` is equal
to the derivative of `λ x, r ^ 2 * arcsin (x / r) + x * sqrt (r ^ 2 - x ^ 2)` everywhere on
`Ioo (-r) r` and that those two functions are continuous, then apply the second fundamental theorem
of calculus with those facts. Some simple algebra then completes the proof.

Note that we choose to define `disc` as a set of points in `ℝ ⨯ ℝ`. This is admittedly not ideal; it
would be more natural to define `disc` as a `metric.ball` in `euclidean_space ℝ (fin 2)` (as well as
to provide a more general proof in higher dimensions). However, our proof indirectly relies on a
number of theorems (particularly `measure_theory.prod.prod_apply`) which do not yet exist for
Euclidean space, thus forcing us to use this less-preferable definition. As `measure_theory.pi`
continues to develop, it should eventually become possible to redefine `disc` and extend our proof
to the n-ball.
-/

section linear_ordered_ring
variables {R : Type*} [linear_ordered_ring R] {x y : R}

lemma abs_lt_abs_of_sqr_lt_sqr (h : x^2 < y^2) : abs x < abs y :=
lt_of_pow_lt_pow 2 (abs_nonneg y) $ by rwa [← @sqr_abs _ _ x, ← @sqr_abs _ _ y] at h

lemma abs_lt_of_sqr_lt_sqr (h : x^2 < y^2) (hy : 0 ≤ y) : abs x < y :=
begin
  rw [← abs_of_nonneg hy],
  exact abs_lt_abs_of_sqr_lt_sqr h,
end

lemma abs_lt_of_sqr_lt_sqr' (h : x^2 < y^2) (hy : 0 ≤ y) : -y < x ∧ x < y :=
abs_lt.mp $ abs_lt_of_sqr_lt_sqr h hy

end linear_ordered_ring

variables {α : Type*} [ordered_comm_monoid α] {a b c d : α}

@[to_additive]
lemma mul_lt_of_mul_lt_left (h : a * b < c) (hle : d ≤ b) : a * d < c :=
lt_of_le_of_lt (mul_le_mul_left' hle a) h

@[to_additive]
lemma lt_of_mul_lt_of_one_le_left (h : a * b < c) (hle : 1 ≤ b) : a < c :=
by simpa only [mul_one] using mul_lt_of_mul_lt_left h hle

open set real filter measure_theory interval_integral
variable {r : ℝ}

/-- A disc of radius `r` is defined as the collection of points `(p.1, p.2)` in `ℝ × ℝ` such that
  `p.1 ^ 2 + p.2 ^ 2 < r ^ 2`.
  Note that this definition is not equivalent to `metric.ball (0 : ℝ × ℝ) r`. This was done
  intentionally because `dist` in `ℝ × ℝ` is defined as the uniform norm, making the `metric.ball`
  in `ℝ × ℝ` a square, not a disc.
  See the module docstring for an explanation of why we don't define the disc in Euclidean space. -/
def disc (r : ℝ) := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}

/-- A disc of radius `r` can be represented as the region between the two curves
  `λ x, - sqrt (r ^ 2 - x ^ 2)` and `λ x, sqrt (r ^ 2 - x ^ 2)`. -/
lemma disc_eq_region_between (hr : 0 ≤ r) :
  disc r = region_between (λ x, -sqrt (r^2 - x^2)) (λ x, sqrt (r^2 - x^2)) (Ioc (-r) r) :=
begin
  ext p,
  simp only [disc, region_between, mem_set_of_eq, mem_Ioo, mem_Ioc, pi.neg_apply],
  split;
  intro h,
  { split,
    { rcases abs_lt_of_sqr_lt_sqr' (lt_of_add_lt_of_nonneg_left h (pow_two_nonneg p.2)) hr,
      -- have h' := abs_lt_abs_of_sqr_lt_sqr (lt_of_add_lt_of_nonneg_left h (pow_two_nonneg p.2)),
      -- obtain ⟨h1, h2⟩ := abs_lt.mp (by rwa abs_of_nonneg hr at h'),
      exact ⟨left, right.le⟩ },
    { rw [add_comm, ← lt_sub_iff_add_lt] at h,
      exact sqr_lt.mp h } },
  { rw [add_comm, ← lt_sub_iff_add_lt],
    exact sqr_lt.mpr h.2 },
end

/-- For convenience we show a fact we will need multiple times throughout the following proofs:
  For any real `a`, `λ x, sqrt (a - x ^ 2)` is a continuous function. -/
lemma continuous_sqrt_sub {a : ℝ} : continuous (λ x, sqrt (a - x ^ 2)) :=
(continuous_const.sub (continuous_pow 2)).sqrt

/-- The disc is a `measurable_set`. -/
theorem measurable_set_disc (hr : 0 ≤ r) : measurable_set (disc r) :=
begin
  rw disc_eq_region_between hr,
  exact measurable_set_region_between continuous_sqrt_sub.neg.measurable
    continuous_sqrt_sub.measurable measurable_set_Ioc,
end

/-- The area of a disc with radius `r` is `π * r ^ 2`. -/
theorem area_disc' (hr : 0 ≤ r) : volume (disc r) = ennreal.of_real (pi * r ^ 2) :=
begin
  let f := λ x, sqrt (r ^ 2 - x ^ 2),
  let F := λ x, r ^ 2 * arcsin (r⁻¹ * x) + x * sqrt (r ^ 2 - x ^ 2),
  suffices : ∫ x in (-r)..r, (λ x, 2 * f x) x = pi * r ^ 2,
  { have H : ∀ {g : ℝ → ℝ}, continuous g → integrable_on g (Ioc (-r) r) :=
      λ g hg, (hg.integrable_on_compact compact_Icc).mono_set Ioc_subset_Icc_self,
    calc volume (disc r)
       = volume (region_between (λ x, -f x) (λ x, f x) (Ioc (-r) r)) :
          by rw disc_eq_region_between hr
   ... = ennreal.of_real (∫ x in Ioc (-r) r, (f - has_neg.neg ∘ f) x) :
          by convert volume_region_between_eq_integral (H continuous_sqrt_sub.neg)
              (H continuous_sqrt_sub) measurable_set_Ioc (λ x hx, neg_le_self (sqrt_nonneg _))
   ... = ennreal.of_real (∫ x in Ioc (-r) r, (λ x, 2 * f x) x) : by simp [two_mul]
   ... = ennreal.of_real (∫ x in (-r)..r, (λ x, 2 * f x) x) : by rw integral_of_le (neg_le_self hr)
   ... = ennreal.of_real (pi * r ^ 2) : by rw this },
  cases hr.eq_or_lt with heq hlt, { simp [← heq] },
  have hderiv : ∀ x ∈ Ioo (-r) r, has_deriv_at F (2 * f x) x,
  { rintros x ⟨hx1, hx2⟩,
    convert ((has_deriv_at_const x (r^2)).mul ((has_deriv_at_arcsin _ _).comp x
      ((has_deriv_at_const x r⁻¹).mul (has_deriv_at_id' x)))).add
        ((has_deriv_at_id' x).mul (((has_deriv_at_id' x).pow.const_sub (r^2)).sqrt _)),
    { have h : sqrt (1 - x ^ 2 / r ^ 2) * r = sqrt (r ^ 2 - x ^ 2),
      { rw [← sqrt_sqr hr, ← sqrt_mul, sub_mul, sqrt_sqr hr, div_mul_eq_mul_div_comm,
            div_self (pow_ne_zero 2 hlt.ne'), one_mul, mul_one],
        simpa only [sub_nonneg, sqrt_sqr hr, div_le_one (pow_two_pos_of_ne_zero r hlt.ne')]
          using (sqr_lt_sqr' hx1 hx2).le },
      field_simp,
      rw [h, mul_left_comm, ← pow_two, neg_mul_eq_mul_neg, mul_div_mul_left (-x^2) _ two_ne_zero,
          add_left_comm, div_add_div_same, tactic.ring.add_neg_eq_sub, div_sqrt, two_mul] },
    { by_contra hnot,
      rw [not_not, eq_neg_iff_eq_neg, ← one_div, div_mul_eq_mul_div, one_mul,
          ← div_neg_eq_neg_div, eq_comm, div_eq_one_iff_eq (neg_ne_zero.mpr hlt.ne')] at hnot,
      exact hx1.ne' hnot },
    { by_contra hnot,
      rw [not_not, ← one_div, div_mul_eq_mul_div, one_mul, div_eq_one_iff_eq hlt.ne'] at hnot,
      exact hx2.ne hnot },
    { simpa only [sub_ne_zero] using (sqr_lt_sqr' hx1 hx2).ne' } },
  have hcont := ((continuous_const.mul (continuous_arcsin.comp
                  ((@continuous_const _ _ _ _ r⁻¹).mul continuous_id))).add
                    (continuous_id.mul continuous_sqrt_sub)).continuous_on,
  have hcont' := (continuous_const.mul continuous_sqrt_sub).continuous_on,
  calc  ∫ x in (-r)..r, (λ x, 2 * f x) x
      = F r - F (-r) : integral_eq_sub_of_has_deriv_at'_of_le (neg_le_self hr) hcont hderiv hcont'
  ... = pi * r ^ 2 : by simpa [F, inv_mul_cancel hlt.ne', ← mul_div_assoc] using mul_comm (r^2) pi,
end
