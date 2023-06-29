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
open_locale topology

/-- `exp (-b * x)` is integrable on `(a, ∞)`. -/
lemma exp_neg_integrable_on_Ioi (a : ℝ) {b : ℝ} (h : 0 < b) :
  integrable_on (λ x : ℝ, exp (-b * x)) (Ioi a) :=
begin
  have : tendsto (λ x, -exp (-b * x) / b) at_top (𝓝 (-0/b)),
  { refine tendsto.div_const (tendsto.neg _) _,
    exact tendsto_exp_at_bot.comp (tendsto_id.neg_const_mul_at_top (right.neg_neg_iff.2 h)) },
  refine integrable_on_Ioi_deriv_of_nonneg' (λ x hx, _) (λ x hx, (exp_pos _).le) this,
  simpa [h.ne'] using ((has_deriv_at_id x).const_mul b).neg.exp.neg.div_const b,
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
