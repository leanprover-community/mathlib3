/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import analysis.special_functions.log.base
import analysis.special_functions.log.deriv
import analysis.calculus.mean_value_mathlib

/-!
# Binary entropy function

Defines the function `h(p)` which gives the entropy of a Bernoulli random variable with probability
`p`. We define the function directly, since it is a useful function as is.
-/
open real

/-- The binary entropy function -/
noncomputable def bin_ent (b p : ℝ) : ℝ := - p * logb b p - (1 - p) * logb b (1 - p)

@[simp] lemma bin_ent_zero {b : ℝ} : bin_ent b 0 = 0 := by simp [bin_ent]
lemma bin_ent_symm {b p : ℝ} : bin_ent b (1 - p) = bin_ent b p :=
  by { rw [bin_ent, sub_sub_cancel, bin_ent], ring }
@[simp] lemma bin_ent_one {b : ℝ} : bin_ent b 1 = 0 := by simp [bin_ent]

lemma bin_ent_nonneg {b p : ℝ} (hb : 1 < b) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ bin_ent b p :=
begin
  have : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ -(x * logb b x),
  { intros x hx₀ hx₁,
    rw [right.nonneg_neg_iff],
    exact mul_nonpos_of_nonneg_of_nonpos hx₀ (logb_nonpos hb hx₀ hx₁) },
  rw [bin_ent, sub_eq_add_neg, neg_mul],
  exact add_nonneg (this _ hp₀ hp₁) (this _ (sub_nonneg_of_le hp₁) (sub_le_self _ hp₀)),
end

/-- An alternate expression for the binary entropy in terms of natural logs, which is sometimes
easier to prove analytic facts about. -/
lemma bin_ent_eq {b p : ℝ} : bin_ent b p = (- (p * log p) + -((1 - p) * log (1 - p))) / log b :=
by rw [bin_ent, logb, logb, neg_mul, sub_eq_add_neg, add_div, mul_div_assoc', mul_div_assoc',
  neg_div, neg_div]

lemma bin_ent_e {p : ℝ} : bin_ent (exp 1) p = - p * log p - (1 - p) * log (1 - p) :=
by rw [bin_ent, logb, logb, log_exp, div_one, div_one]

private lemma bin_ent_deriv_aux (x : ℝ) (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) :
  has_deriv_at (λ y, - (y * log y) + -((1 - y) * log (1 - y))) (log (1 - x) - log x) x :=
begin
  have h : ∀ x : ℝ, x ≠ 0 → has_deriv_at (λ y, - (y * log y)) (- (log x + 1)) x,
  { rintro x hx₀,
    refine has_deriv_at.neg _,
    have : 1 * log x + x * x⁻¹ = log x + 1,
    { rw [one_mul, mul_inv_cancel hx₀] },
    rw ←this,
    exact has_deriv_at.mul (has_deriv_at_id' x) (has_deriv_at_log hx₀) },
  suffices : has_deriv_at (λ y, - (y * log y) + -((1 - y) * log (1 - y)))
    (- (log x + 1) + (- (log (1 - x) + 1) * -1)) x,
  { convert this using 1,
    ring_nf },
  have : has_deriv_at (λ y : ℝ, 1 - y) (-1 : ℝ) x :=
    (has_deriv_at_id' x).const_sub 1,
  refine has_deriv_at.add (h _ hx₀) _,
  exact (h (1 - x) (sub_ne_zero_of_ne hx₁.symm)).comp x ((has_deriv_at_id' x).const_sub 1),
end
