/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import measure_theory.integral.interval_integral

import analysis.special_functions.exponential
import analysis.special_functions.integrals
import measure_theory.integral.integral_eq_improper


/-!
# Integrals with exponential decay at ∞

As easy special cases of general theorems in the library, we prove the following test
for integrability:

* `exp_decay.integrable_bigoh_exp`: If `f` is continuous on `[a,∞)`, for some `a ∈ ℝ`, and there
  exists `b > 0` such that `f(x) = O(exp(-b x))` as `x → ∞`, then `f` is integrable on `(a, ∞)`.

-/

noncomputable theory
open real interval_integral measure_theory set filter

namespace exp_decay

/-- `exp(-b x)` is integrable on `(a, X]` for any finite `a`, `X`. -/
lemma exp_neg_finite_integrable (b : ℝ) (a : ℝ) (X : ℝ):
  integrable_on (λ x : ℝ, exp(-b * x) ) (Ioc a X) :=
  (continuous_const.mul continuous_id).exp.integrable_on_Ioc

/-- The antiderivative of `exp(-b x)` is what it should be. -/
lemma exp_neg_hasderiv (b : ℝ) (x : ℝ) (h : 0 < b) :
  has_deriv_at (λ (y : ℝ), -exp (-b * y) / b) (exp (-b * x)) x :=
begin
  have : has_deriv_at (λ (x : ℝ), x) 1 x := has_deriv_at_id x,
  have : has_deriv_at (λ (x : ℝ), b*x) b x := by simpa only [mul_one] using
    has_deriv_at.const_mul b this,
  have : has_deriv_at (λ (x : ℝ), -b*x) (-b) x := by simpa only [neg_mul] using this.neg,
  have : has_deriv_at (λ (x : ℝ), exp (-b*x)) (exp (-b*x)*(-b)) x := has_deriv_at.exp this,
  have : has_deriv_at (λ (x : ℝ), -exp (-b*x)) (-(exp (-b*x)*(-b))) x := has_deriv_at.neg this,
  have := (has_deriv_at.div_const this b),
  have s : (-(exp (-b * x) * -b) / b) = exp(-b*x),
  { simp only [neg_mul, mul_neg, neg_neg],
    rw mul_div_cancel _ (h.ne') },
  rw s at this, exact this
end

/-- Integral of `exp(-b x)` over `(a, X)` is bounded as `X → ∞`. -/
lemma exp_neg_integral_bound {b : ℝ} (a X : ℝ) (h2 : 0 < b):
  (∫ x in a .. X, exp (-b * x)) ≤ exp(-b*a)/b :=
begin
  rw (integral_deriv_eq_sub' (λ x:ℝ, -exp(-b*x)/b ) ),
  -- goal 1/4: F(X) - F(a) is bounded
  { simp only [tsub_le_iff_right],
    rw (neg_div b (exp (-b * a))),
    rw (neg_div b (exp (-b * X))),
    rw add_neg_self,
    rw [neg_le, neg_zero],
    apply le_of_lt,
    apply div_pos,
    apply exp_pos,
    exact h2 },
  -- goal 2/4: the derivative of F is exp(-b x)
  { ext1, exact has_deriv_at.deriv ( exp_neg_hasderiv b x h2 ), },
  -- goal 3/4: F is differentiable (why isn't this implicit?)
  { intros x hx, exact has_deriv_at.differentiable_at (exp_neg_hasderiv b x h2 ),},
  -- goal 4/4: exp(-b x) is continuous
  { apply continuous.continuous_on, continuity }
end

/-- `exp(-b x)` is integrable on `(a, ∞)`. -/
lemma exp_neg_integrable_Ioi (a : ℝ) {b : ℝ} (h : 0 < b):
  integrable_on (λ x : ℝ, exp(-b * x)) (Ioi a) :=
begin
  apply (integrable_on_Ioi_of_interval_integral_norm_bounded
    (exp (-b*a)/b) a (exp_neg_finite_integrable b a) tendsto_id),
  simp only [eventually_at_top, ge_iff_le],
  use a,
  intros b2 hb2,
  have : (λ x:ℝ, ∥exp(-b * x)∥) = (λ x:ℝ, exp(-b * x)),
  { ext1,apply norm_of_nonneg,
    exact (exp_pos (-b*x)).le },
  rw this,
  exact exp_neg_integral_bound a b2 h,
end

lemma exp_neg_finite_integral_Ioi (a : ℝ) {b : ℝ} (h : 0 < b):
  has_finite_integral (λ x : ℝ, exp(-b * x))
  (measure_space.volume.restrict (Ioi a)) :=
begin
  apply integrable.has_finite_integral,
  exact exp_neg_integrable_Ioi a h,
end

/-- If `f` is continuous on `[a, ∞)`, and is `O(exp(-b x))` at `∞` for some `b > 0`, then
`f` is integrable on `(a, ∞)`. -/
lemma integrable_bigoh_exp (f: ℝ → ℝ) (a : ℝ) {b : ℝ} (h0 : 0 < b) (h1: continuous_on f (Ici a) )
  (h2: asymptotics.is_O f (λ x:ℝ, exp(-b * x)) at_top) : integrable_on f (Ioi a) :=
begin
  cases (asymptotics.is_O.is_O_with h2) with c h3,
  rw [asymptotics.is_O_with_iff,eventually_at_top] at h3,
  cases h3 with r bdr,
  let v := max a r,

  have int_left: integrable_on f (Ioc a v),
  { rw ←(interval_integrable_iff_integrable_Ioc_of_le (le_max_left a r)),
    have u : Icc a v ⊆ Ici a := Icc_subset_Ici_self,
    exact continuous_on.interval_integrable_of_Icc (le_max_left a r) (continuous_on.mono h1 u),},
  suffices: integrable_on f (Ioi v),
  { have un: (Ioc a v) ∪ (Ioi v) = Ioi a := by simp only [Ioc_union_Ioi_eq_Ioi,
      le_max_iff, le_refl, true_or],
    have t:= integrable_on_union.mpr ⟨int_left, this⟩,
    rw un at t,
    exact t },

  split,
  { exact continuous_on.ae_measurable (continuous_on.mono h1 $ Ioi_subset_Ici $ le_max_left a r)
      measurable_set_Ioi, },
   -- now have to show "has_finite_integral f"
  have : has_finite_integral (λ x : ℝ, c * exp (-b * x)) (volume.restrict(Ioi v)),
  { apply has_finite_integral.const_mul,
    exact exp_neg_finite_integral_Ioi v h0 },
  apply measure_theory.has_finite_integral.mono this,
  -- Check "everywhere bounded" implies "almost everywhere bounded"
  rw ae_restrict_iff',
  swap, apply measurable_set_Ioi,
  apply ae_of_all,

  intros x h1x,
  rw [Ioi, mem_set_of_eq] at h1x,
  specialize bdr x (le_trans (le_max_right a r) h1x.le ),
  refine (le_trans bdr _),
  rw norm_mul,
  apply mul_le_mul_of_nonneg_right,
  { rw norm_eq_abs, exact le_abs_self c,},
  { rw norm_eq_abs, apply abs_nonneg, }
end

end exp_decay
