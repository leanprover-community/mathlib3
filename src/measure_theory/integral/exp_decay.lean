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

lemma exp_neg_hasderiv (b : ℝ) (x : ℝ) (h : 0 < b) :
  has_deriv_at (λ (y : ℝ), -exp (-b * y) / b) (exp (-b * x)) x :=
begin
  have : has_deriv_at (λ (x : ℝ), x) 1 x := has_deriv_at_id x,
  have : has_deriv_at (λ (x : ℝ), b*x) b x := by simpa using has_deriv_at.const_mul b this,
  have : has_deriv_at (λ (x : ℝ), -b*x) (-b) x := by simpa using has_deriv_at.neg this,
  have : has_deriv_at (λ (x : ℝ), exp (-b*x)) (exp (-b*x)*(-b)) x := has_deriv_at.exp this,
  have : has_deriv_at (λ (x : ℝ), -exp (-b*x)) (-(exp (-b*x)*(-b))) x := has_deriv_at.neg this,
  have := (has_deriv_at.div_const this b),
  have s : (-(exp (-b * x) * -b) / b) = exp(-b*x),
  { simp only [neg_mul, mul_neg, neg_neg],
    rw mul_div_cancel _ (h.ne') },
  rw s at this, exact this
end

lemma exp_neg_antideriv {b: ℝ} (h: 0 < b):
  deriv (λ (x : ℝ), -exp (-b * x) / b) = (λ (x : ℝ), exp (-b * x)) :=
begin
  ext1,
  exact has_deriv_at.deriv ( exp_neg_hasderiv b x h )
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
  exact exp_neg_antideriv h2,
  -- goal 3/4: F is differentiable (why isn't this implicit?)
  intros x hx,
  exact has_deriv_at.differentiable_at (exp_neg_hasderiv b x h2 ),
  -- goal 4/4: exp(-b x) is continuous
  { apply continuous.continuous_on,
    continuity }
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
  apply exp_neg_integral_bound,
  exact h
end

lemma exp_neg_finite_integral_Ioi (a : ℝ) {b : ℝ} (h : 0 < b):
  has_finite_integral (λ x : ℝ, exp(-b * x))
  (measure_space.volume.restrict (Ioi a)) :=
begin
  apply integrable.has_finite_integral,
  exact exp_neg_integrable_Ioi a h,
end

/- Now show any continous function which is O(exp(-b x)) is integrable. -/

lemma globalbound_bigoh_exp (f: ℝ → ℝ) (a : ℝ) (b : ℝ) (h : 0 < b)
  (h1: continuous_on f (Ici a) )
  (h2: asymptotics.is_O f (λ x:ℝ, exp(-b * x)) at_top) :
  ∃ (B : ℝ), ∀ (x : ℝ), (x ∈ Ici a) → |f(x)| ≤ B * exp(-b*x)  :=
begin
  have h3 := asymptotics.is_O.is_O_with h2,
  cases h3 with c h3,
  rw asymptotics.is_O_with_iff at h3,
  rw eventually_at_top at h3,
  cases h3 with r bdr,
  let v := max a r,

  -- extract an upper bound for |f(x)| on Icc(a, v) by continuity
  -- this needs golfing
  have cts_left : continuous_on (λ y:ℝ, |f(y)|) (Icc a v) :=
    (continuous_on.mono (continuous_on.abs h1) Icc_subset_Ici_self),
  have icc_non : (Icc a v).nonempty := by { rw nonempty_Icc, exact le_max_left a r },
  have z := is_compact.exists_forall_ge is_compact_Icc icc_non cts_left,
  simp only [exists_prop] at z,
  cases z with z hz,
  let C1 := |f(z)| * exp(b * v),

  have bound1 : ∀ x : ℝ, (x ∈ Icc a v) → |f(x)| ≤ (C1 * exp(-b * x)),
  { intro x, cases hz with hz0 hz1,
    specialize hz1 x,
    intro dummy,
    have hz1 := hz1(dummy),
    have : exp(-b * v) ≤ exp(-b * x),
    { rw exp_le_exp,
      rw neg_mul,rw neg_mul,
      apply neg_le_neg,
      apply mul_le_mul_of_nonneg_left,
      exact dummy.2, exact le_of_lt(h) },
    have this2: |f(x)| ≤ C1 * exp(-b * v),
    { apply le_trans hz1, apply le_of_eq,
      rw neg_mul,
      rw exp_neg,
      have : C1*(exp (b*v))⁻¹ = |f(z)|,
      apply mul_div_cancel,
      exact (exp_pos (b*v)).ne',
      rw this },
    apply (le_trans this2 _),
    apply mul_le_mul_of_nonneg_left this,
    apply mul_nonneg,
    apply abs_nonneg,
    apply le_of_lt(exp_pos (b*v)) },
  clear icc_non cts_left hz,

  let C := max C1 c,
  use C,
  intros x hx,
  by_cases (x ≤ v),
  specialize bound1 x,
  have : x ∈ Icc a v,
  { split, exact hx, exact h },
  specialize bound1 this,
  have : C1 * exp (-b * x) ≤ C * exp(-b * x),
  { apply mul_le_mul_of_nonneg_right,
    simp,
    apply le_of_lt(exp_pos (-b * x)) },
  exact le_trans bound1 this,
  have h : (r ≤ x),
  { have : r ≤ v := le_max_right a r,
    linarith },
  specialize bdr x h,
  apply le_trans bdr,
  have : ∥exp(-b * x)∥ = exp(-b * x),
  { apply abs_of_nonneg,
    apply le_of_lt(exp_pos (-b * x)) },
  rw this,
  apply (mul_le_mul_of_nonneg_right (le_max_right C1 c) (le_of_lt(exp_pos (-b * x))))
end

/-- If `f` is continuous on `[a, ∞)`, and is `O(exp(-b x))` at `∞` for some `b > 0`, then
`f` is integrable on `(a, ∞)`. -/
lemma integrable_bigoh_exp (f: ℝ → ℝ) (a : ℝ) {b : ℝ} (h0 : 0 < b)
  (h1: continuous_on f (Ici a) )
  (h2: asymptotics.is_O f (λ x:ℝ, exp(-b * x)) at_top)
  : integrable_on f (Ioi a) :=
begin
  have t := globalbound_bigoh_exp f a b h0 h1 h2,
  cases t with C t,

  rw [integrable_on,integrable],
  split,
  apply continuous_on.ae_measurable (continuous_on.mono h1 Ioi_subset_Ici_self) measurable_set_Ioi,

  -- now have to show "has_finite_integral f"
  have : has_finite_integral (λ x : ℝ, C * exp (-b * x)) (volume.restrict(Ioi a)),
  { apply has_finite_integral.const_mul,
    exact exp_neg_finite_integral_Ioi a h0 },

  apply measure_theory.has_finite_integral.mono this,

  -- Check "everywhere bounded" implies "almost everywhere bounded"
 have : (Ioi a) ∈ (volume.restrict (Ioi a)).ae,
  { apply ae_iff.2,
    rw measure.restrict_apply,
    have : {a_1 : ℝ | ¬a < a_1} ∩ Ioi a = ∅ := by { ext, simp },
    rw this,
    apply measure_empty,
    simp only [not_lt],
    apply measurable_set_Iic },
  apply eventually_of_mem this,

  intros x h1x,
  specialize t x (le_of_lt h1x),
  rw norm_eq_abs, rw norm_eq_abs,
  rw le_abs,left,exact t
end


end exp_decay
