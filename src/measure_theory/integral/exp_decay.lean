/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import measure_theory.integral.interval_integral
import measure_theory.integral.integral_eq_improper

/-!
# Integrals with exponential decay at ∞

As easy special cases of general theorems in the library, we prove the following test
for integrability:

* `integrable_of_is_O_exp_neg`: If `f` is continuous on `[a,∞)`, for some `a ∈ ℝ`, and there
  exists `b > 0` such that `f(x) = O(exp(-b x))` as `x → ∞`, then `f` is integrable on `(a, ∞)`.
-/

noncomputable theory
open real interval_integral measure_theory set filter

/-- Integral of `exp (-b * x)` over `(a, X)` is bounded as `X → ∞`. -/
lemma integral_exp_neg_le {b : ℝ} (a X : ℝ) (h2 : 0 < b) :
  (∫ x in a .. X, exp (-b * x)) ≤ exp (-b * a) / b :=
begin
  rw integral_deriv_eq_sub' (λ x, -exp (-b * x) / b),
  -- goal 1/4: F(X) - F(a) is bounded
  { simp only [tsub_le_iff_right],
    rw [neg_div b (exp (-b * a)), neg_div b (exp (-b * X)), add_neg_self, neg_le, neg_zero],
    exact (div_pos (exp_pos _) h2).le, },
  -- goal 2/4: the derivative of F is exp(-b x)
  { ext1, simp [h2.ne'] },
  -- goal 3/4: F is differentiable
  { intros x hx, simp [h2.ne'], },
  -- goal 4/4: exp(-b x) is continuous
  { apply continuous.continuous_on, continuity }
end

/-- `exp (-b * x)` is integrable on `(a, ∞)`. -/
lemma exp_neg_integrable_on_Ioi (a : ℝ) {b : ℝ} (h : 0 < b) :
  integrable_on (λ x : ℝ, exp (-b * x)) (Ioi a) :=
begin
  have : ∀ (X : ℝ), integrable_on (λ x : ℝ, exp (-b * x) ) (Ioc a X),
  { intro X, exact (continuous_const.mul continuous_id).exp.integrable_on_Ioc },
  apply (integrable_on_Ioi_of_interval_integral_norm_bounded (exp (-b * a) / b) a this tendsto_id),
  simp only [eventually_at_top, norm_of_nonneg (exp_pos _).le],
  exact ⟨a, λ b2 hb2, integral_exp_neg_le a b2 h⟩,
end

/-- If `f` is continuous on `[a, ∞)`, and is `O (exp (-b * x))` at `∞` for some `b > 0`, then
`f` is integrable on `(a, ∞)`. -/
lemma integrable_of_is_O_exp_neg {f : ℝ → ℝ} {a b : ℝ} (h0 : 0 < b)
  (h1 : continuous_on f (Ici a)) (h2 : f =O[at_top] (λ x, exp (-b * x))) :
  integrable_on f (Ioi a) :=
begin
  cases h2.is_O_with with c h3,
  rw [asymptotics.is_O_with_iff, eventually_at_top] at h3,
  cases h3 with r bdr,
  let v := max a r,
  -- show integrable on `(a, v]` from continuity
  have int_left : integrable_on f (Ioc a v),
  { rw ←(interval_integrable_iff_integrable_Ioc_of_le (le_max_left a r)),
    have u : Icc a v ⊆ Ici a := Icc_subset_Ici_self,
    exact (h1.mono u).interval_integrable_of_Icc (le_max_left a r), },
  suffices : integrable_on f (Ioi v),
  { have t : integrable_on f (Ioc a v ∪ Ioi v) := integrable_on_union.mpr ⟨int_left, this⟩,
    simpa only [Ioc_union_Ioi_eq_Ioi, le_max_iff, le_refl, true_or] using t },
  -- now show integrable on `(v, ∞)` from asymptotic
  split,
  { exact (h1.mono $ Ioi_subset_Ici $ le_max_left a r).ae_strongly_measurable measurable_set_Ioi },
  have : has_finite_integral (λ x : ℝ, c * exp (-b * x)) (volume.restrict (Ioi v)),
  { exact (exp_neg_integrable_on_Ioi v h0).has_finite_integral.const_mul c },
  apply this.mono,
  refine (ae_restrict_iff' measurable_set_Ioi).mpr _,
  refine ae_of_all _ (λ x h1x, _),
  rw [norm_mul, norm_eq_abs],
  rw [mem_Ioi] at h1x,
  specialize bdr x ((le_max_right a r).trans h1x.le),
  exact bdr.trans (mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg _))
end
