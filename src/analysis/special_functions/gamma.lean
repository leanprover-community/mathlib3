/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import analysis.special_functions.exponential
import measure_theory.integral.integral_eq_improper
import measure_theory.integral.limit_comparison
import analysis.special_functions.integrals

/-!
# The Gamma function

In this file we define the Γ function (of a real variable in the range `1 ≤ s`), using the
definition `Γ(s) = ∫ x in 0..∞, x^(s-1) exp(-x) dx`, and prove that it is continuous and satisfies
the relation `Γ(s+1) = s Γ(s)`. We also prove that `Γ(n+1) = n!` for `n ∈ ℕ`.

TO DO:

- Extend to the whole real line.
- Allow complex `s` and prove analyticity.

## Tags

gamma
-/

noncomputable theory
open filter interval_integral set real measure_theory
open_locale topological_space filter measure_theory

namespace real.gamma


/-- Integrand for the Gamma function integral -/
def integrand (s x : ℝ) : ℝ := exp(-x) * x^s

/- We prove some lemmas about this integrand F:

- for any `s ≥ 0`, F is continuous of `x ∈ [0,∞)`;
- for any `s ≥ 1`, the derivative of `F(s, -)` at any `x ∈ [0, ∞)` is what it should be;
- for any `s ≥ 1`, the derivative of `F(s, -)` is integrable on [0, X] for any X ≥ 0;
- for any `s ∈ ℝ`, F is `O( exp(-(1/2) * x))` as `x → ∞`.
-/

lemma cont_integrand (s : ℝ) (h1: 0 ≤ s) : continuous_on (integrand s) (Ici 0) :=
continuous_on_id.neg.exp.mul $ continuous_on_id.rpow_const $ λ _ _, or.inr h1

lemma deriv_integrand (s x: ℝ) (h1: 1 ≤ s) : has_deriv_at (integrand s)
(- (exp (-x) * x ^ s) + exp (-x) * (s * x ^ (s - 1))) x :=
begin
  have d1 : has_deriv_at (λ (y: ℝ), exp(-y)) (-exp(-x)) x,
  { simpa using has_deriv_at.exp (has_deriv_at_neg x) },
  simpa using (has_deriv_at.mul d1 $ has_deriv_at_rpow_const $ or.inr h1),
end

lemma deriv_interval_integrable (s X: ℝ) (hs: 1 ≤ s):
interval_integrable (λ (x : ℝ),  -(exp (-x) * x ^ s) + exp (-x) * (s * x ^ (s - 1)))
  measure_space.volume 0 X :=
begin
  apply continuous_on.interval_integrable,

  have c : continuous_on (λ (x : ℝ), exp (-x)) (interval 0 X),
  { apply continuous_on.exp,
    apply continuous_on.neg,
    apply continuous_on_id },

  -- This is a bit of a mess, proving continuity of a function built up as a sum of many terms.
  apply continuous_on.add,
  { apply continuous_on.neg,
    apply continuous_on.mul c,
    apply continuous_on.rpow_const,
    { apply continuous_at.continuous_on,
      intros x hxX,
      apply continuous_at_id },
    { intros x hxX,
      right,
      exact le_trans(zero_le_one)(hs) } },
  -- halfway...
  { apply continuous_on.mul c,
    refine continuous_on.mul (continuous.continuous_on continuous_const)
      (continuous_on.rpow_const (continuous_at.continuous_on _) _),
    { intros x hxX,
      apply continuous_at_id },
    { intros x hxX,
      right,
      exact sub_nonneg.mpr hs } },
end

/-- The gamma integrand is O(exp(-(1/2) * x)) at top for any fixed s -/
lemma asymp_integrand (s : ℝ) :
  asymptotics.is_O (integrand s) (λ x : ℝ, exp(-(1/2) * x)) filter.at_top :=
begin
  apply asymptotics.is_o.is_O,
  apply asymptotics.is_o_of_tendsto,
  { intros x hx,
    exfalso,
    apply ( exp_pos(-(1/2) * x)).ne',
    exact hx },
  simp only [integrand],

  have : ∀ (x: ℝ), (x > 0) → (exp (-x) * x ^ s / exp (-(1 / 2) * x) = exp (-(1/2) * x) * x ^ s),
  { intros x h,
    rw mul_comm,
    rw mul_comm (exp (-(1/2) * x)) (x ^ s),
    rw div_eq_of_eq_mul,
    exact (exp_pos (-(1/2) * x)).ne',
    have: exp(-x) = exp(-(1/2)*x) * exp (-(1 / 2) * x),
    { rw ←real.exp_add,
      simp only [real.exp_eq_exp],
      ring, },
    rw [this, mul_assoc], },
  replace : eventually_eq at_top
    (λ x:ℝ,(exp (-x) * x ^ s / exp (-(1 / 2) * x))) (λ x:ℝ,  exp (-(1/2) * x) * x ^ s),
  { apply eventually_eq_of_mem (Ioi_mem_at_top(0:ℝ)),
    intros x hx,
    rw [set.Ioi, mem_set_of_eq] at hx,
    exact (this x hx) },
  rw (tendsto_congr' this),
  have : (λ (x : ℝ), exp (-(1 / 2) * x) * x ^ s) = (λ (x : ℝ), exp ((1 / 2) * x) / x ^ s)⁻¹,
  { ext1,
    simp only [neg_mul, pi.inv_apply],
    rw inv_div,
    rw exp_neg,
    ring },
  rw this,
  apply tendsto.inv_tendsto_at_top,
  exact (tendsto_exp_mul_div_rpow_at_top s (1/2))(one_half_pos), -- hooray!
end

lemma loc_unif_bound (s t x : ℝ) (ht : t ∈ set.Icc 0 s ) (hx : x ∈ set.Ioi (0:ℝ)) :
  integrand t x ≤  integrand s x + integrand 0 x :=
begin
  rw [set.Ioi,mem_set_of_eq] at hx,
  rw [set.Icc,mem_set_of_eq] at ht,
  by_cases (1 ≤ x),
  { suffices: integrand t x ≤ integrand s x, -- case 1 ≤ x
    { suffices: 0 ≤ integrand 0 x,
      { linarith },
      simp only [integrand, rpow_zero, mul_one],
      exact le_of_lt(exp_pos (-x)) },
    simp only [integrand],
    apply mul_le_mul,
    refl,
    apply rpow_le_rpow_of_exponent_le h ht.2,
    apply le_of_lt,
    apply rpow_pos_of_pos,
    linarith,
    exact le_of_lt(exp_pos (-x)) },
  { simp only [not_le] at h, -- case x < 1
    suffices: integrand t x ≤ integrand 0 x,
    { suffices: 0 ≤ integrand s x,
      { linarith },
      apply le_of_lt,
      apply mul_pos,
      apply exp_pos,
      apply rpow_pos_of_pos hx },
    simp only [integrand],
    rw [rpow_zero, mul_one],
    rw mul_le_iff_le_one_right,
    apply rpow_le_one,
    exact le_of_lt hx,
    exact le_of_lt h,
    exact ht.1,
    exact exp_pos (-x) },
end

/-- The (lower) incomplete Γ function, Γ(s, X) = ∫ x ∈ 0..X, exp(-x) x^(s-1). -/
def incomplete_gamma (s X : ℝ) : ℝ := ∫ x in 0..X, exp(-x) * x^(s-1)

/-- Recurrence relation for the incomplete Γ function. -/
lemma incomplete_gamma_recurrence (s X : ℝ) (h: 1 ≤ s) (h2: 0 ≤ X):
  incomplete_gamma (s+1) X = s * incomplete_gamma s X - X^s * exp(-X) :=
begin
  rw incomplete_gamma,
  rw incomplete_gamma,

  have F_der_I: (∀ (x:ℝ), (x ∈ interval 0 X) →
    has_deriv_at (integrand s) (- (exp (-x) * x ^ s) + exp (-x) * (s * x ^ (s - 1))) x),
  { intros x hx,
    exact deriv_integrand s x h },

  have int_eval := integral_eq_sub_of_has_deriv_at F_der_I (deriv_interval_integrable s X h),

  have : (integrand s 0) = 0,
  { rw integrand, rw zero_rpow, ring, apply ne_of_gt,
    apply lt_of_lt_of_le zero_lt_one h },
  rw [this, integrand] at int_eval,
  simp only [sub_zero] at int_eval,
  rw interval_integral.integral_add at int_eval,
  { simp only [add_tsub_cancel_right],
    have : (∫ (x : ℝ) in 0..X, exp (-x) * x ^ s)
      = (∫ (x : ℝ) in 0..X, exp (-x) * (s * x ^ (s - 1))) - exp (-X) * X ^ s,
    { rw sub_eq_neg_add,
      apply eq_add_of_add_neg_eq,
      rw ← int_eval,
      simp only [interval_integral.integral_neg, neg_add_rev, neg_neg], ring },
    rw this,
    have : (exp (-X) * X ^ s) = (X^s * exp(-X)) := by ring,
    rw this,
    simp only [sub_left_inj],

    have : (λ (x : ℝ), exp (-x) * (s * x ^ (s - 1))) = (λ (x : ℝ), s * (exp (-x) * x ^ (s - 1))),
    { ext1, ring },
    rw this,
    apply integral_const_mul },

  -- now two more integrability statements, yawn
  { apply continuous_on.interval_integrable,
    have := cont_integrand s (le_trans zero_le_one h),
    replace := continuous_on.neg this,
    have ss : (interval 0 X) ⊆ (set.Ici 0),
    { rw interval,
      rw [max_def, min_def],
      rw Icc_subset_Ici_iff,
      { split_ifs,tauto,tauto },
      { split_ifs, tauto,tauto,tauto,tauto } },
    exact continuous_on.mono this ss },

  -- and the last one
  { apply continuous_on.interval_integrable,
    apply continuous_on.mul,
    apply continuous_on.exp,
    apply continuous_on.neg,
    apply continuous_on_id,
    apply continuous_on.mul,
    apply continuous_on_const,
    apply continuous_on.rpow_const,
    apply continuous_on_id,
    intros x hx,
    right,
    rw le_sub,
    simp only [sub_zero],
    exact h },
end

lemma integrable_integrand (s: ℝ) (h: 1 ≤ s): integrable_on
  (λ (x:ℝ), exp(-x) * x^(s-1)) (Ioi 0) :=
begin
  apply limit_comparison.integrable_bigoh_exp (integrand $ s-1) 0 one_half_pos,
  apply cont_integrand,
  { linarith },
  exact asymp_integrand (s-1)
end

/-- The Γ function, defined by the integral ∫ x = 0..∞, exp(-x) * x^(s-1).

This definition is valid for s > 0, but we only prove convergence of the integral for s ≥ 1. -/
def real_gamma (s: ℝ) : ℝ :=  ∫ x in (Ioi 0), exp(-x) * x^(s-1)

lemma tendsto_incomplete_gamma (s : ℝ) (h: 1 ≤ s):
  tendsto (incomplete_gamma s) (filter.at_top)  (𝓝 $ real_gamma s) :=
begin
  apply interval_integral_tendsto_integral_Ioi,
  swap, apply tendsto_id,
  exact integrable_integrand s h
end

lemma gamma_recurrence (s : ℝ) (h: 1 ≤ s) :
  real_gamma (s+1) = s * real_gamma s :=
begin
  have t1: tendsto (incomplete_gamma (s+1)) at_top (𝓝 (real_gamma (s+1))),
  { apply tendsto_incomplete_gamma, linarith },
  suffices t2: tendsto (incomplete_gamma (s+1)) at_top (𝓝 $ s * real_gamma s),
  { apply tendsto_nhds_unique t1 t2 },

  have a: eventually_eq at_top (incomplete_gamma (s+1))
    (λ X:ℝ, s * incomplete_gamma s X - X^s * exp(-X)),
  { apply eventually_eq_of_mem (Ici_mem_at_top (0:ℝ)),
    intros X hX,
    rw [set.Ici, mem_set_of_eq] at hX,
    exact incomplete_gamma_recurrence s X h hX },
  replace a := eventually_eq.symm a,

  suffices b: tendsto (λ X:ℝ, s * incomplete_gamma s X - X^s * exp(-X)) at_top
    (𝓝 $ s * real_gamma s),
  { exact tendsto.congr' a b, },

  have l1: tendsto (λ X:ℝ, s * incomplete_gamma s X) at_top (𝓝 $ s * real_gamma s),
  { apply tendsto.const_mul,
    exact tendsto_incomplete_gamma s h },
  suffices l2: tendsto (λ X:ℝ, -X^s * exp(-X)) at_top (𝓝 $ (0:ℝ)),
  { have := tendsto.add l1 l2,
    simpa using this },
  have l3: tendsto (λ X:ℝ, X^s * exp(-X)) at_top (𝓝 $ (0:ℝ)),
  { have := tendsto_rpow_mul_exp_neg_mul_at_top_nhds_0 s (1:ℝ) zero_lt_one,
    simpa using this },
  have: (λ X:ℝ, -X^s * exp(-X)) = (λ X:ℝ, (-1) * (X^s * exp(-X))) :=
    by { simp only [neg_mul, one_mul] },
  rw this,
  have : (0:ℝ) = (-1) * (0:ℝ) := by {ring, },
  rw this,
  apply tendsto.const_mul,
  exact l3
end

lemma incomplete_gamma_at_one: incomplete_gamma 1 = (λ X:ℝ, 1 - exp(-X) ) :=
begin
  ext,
  rw incomplete_gamma,
  simp only [sub_self, rpow_zero, mul_one, integral_comp_neg,
    neg_zero, integral_exp, real.exp_zero],
end

lemma gamma_at_one: real_gamma 1 = 1 :=
begin
  have t1: tendsto (incomplete_gamma 1) at_top (𝓝 $ real_gamma 1),
  { apply tendsto_incomplete_gamma, refl },
  have t2: tendsto (incomplete_gamma 1) at_top (𝓝 1),
  { rw incomplete_gamma_at_one,
    have : tendsto (λ X, exp(-X)) at_top (𝓝 0),
    { simpa using tendsto_rpow_mul_exp_neg_mul_at_top_nhds_0 0 1 },
    simpa only [sub_zero] using tendsto.const_sub 1 this, },
  apply tendsto_nhds_unique t1 t2,
end

lemma gamma_integer: ∀ n:ℕ, real_gamma (n+1) = nat.factorial n :=
begin
  intro n,
  induction n with n hn,

  simp only [nat.cast_zero, zero_add, nat.factorial_zero, nat.cast_one],
  exact gamma_at_one,

  rw gamma_recurrence,
  simp only [nat.cast_succ, nat.factorial_succ, nat.cast_mul, mul_eq_mul_left_iff],
  left, exact hn,

  simp only [nat.cast_succ, le_add_iff_nonneg_left, nat.cast_nonneg]
end


/- Continuity of the gamma function. This is proved using `continuous_at_of_dominated`, so
we need to verify the hypotheses. -/
lemma gamma_cts_Ioi: continuous_on real_gamma (Ioi 1):=
begin

  apply continuous_at.continuous_on,
  intros s hs,
  rw [set.Ioi, mem_set_of_eq] at hs,

  have Ioo_nhd: Ioo 1 (s+1) ∈ 𝓝 s,
  { apply Ioo_mem_nhds,
    linarith, linarith },

  -- F(t-1, -) is bounded, locally uniformly in t near s
  have bound: ∀ᶠ (t : ℝ) in 𝓝 s, ∀ᵐ (x : ℝ) ∂ measure_space.volume.restrict (Ioi 0),
    ∥exp (-x) * x ^ (t - 1)∥ ≤ (λ  y:ℝ, integrand s y + integrand 0 y) x,
  { apply eventually_of_mem (Ioo_nhd),
    intros t ht,
    rw [set.Ioo, mem_set_of_eq] at ht,

    rw ae_iff,
    rw measure.restrict_apply',
    swap, apply measurable_set_Ioi,
    suffices: ({x : ℝ | ¬ ∥exp (-x) * x ^ (t - 1)∥ ≤ integrand s x + integrand 0 x}
      ∩ Ioi 0) = ∅,
    { rw this,
      apply measure_empty },
    ext,
    simp only [not_le, mem_inter_eq, mem_set_of_eq, set.mem_Ioi,
      mem_empty_eq, iff_false, not_and, not_lt],
    contrapose,
    simp only [not_le, not_lt],
    intro hx,
    have: ∥exp(-x) * x^(t-1)∥ = exp(-x) * x^(t-1),
    { apply abs_of_nonneg,
      apply le_of_lt,
      apply mul_pos,
      exact exp_pos (-x),
      apply rpow_pos_of_pos,
      exact hx },
    rw this,
    have: exp(-x) * x^(t-1) ≤ integrand s x + integrand 0 x,
    { apply loc_unif_bound s (t-1) x,
      { rw [set.Icc,mem_set_of_eq],
      split,
      linarith, linarith,},
      tauto, },
    exact this },

  -- The upper bound is integrable
  have bd_integrable: integrable (λ (x : ℝ), integrand s x + integrand 0 x)
  (measure_space.volume.restrict (Ioi 0)),
  { apply integrable.add,
    { have: 1 ≤ s+1,
      { linarith },
      replace := integrable_integrand (s+1) this,
      simpa using this },
    { have := integrable_integrand (1:ℝ) (le_refl (1:ℝ)),
      rw sub_self at this,
      exact this } },

  -- F(t-1, -) is a.e. measurable in x, for all t near s
  have ae_meas: ∀ᶠ (t : ℝ) in 𝓝 s, ae_measurable (λ (x : ℝ), exp (-x) * x ^ (t - 1))
    (measure_space.volume.restrict (Ioi 0)),
  { apply eventually_of_mem (Ioi_mem_nhds hs),
    intros t ht,
    rw [set.Ioi, mem_set_of_eq] at ht,
    refine continuous_on.ae_measurable _ measurable_set_Ioi,
    apply continuous_on.mono (cont_integrand (t-1) (by linarith)),
    rw [set.Ioi, set.Ici, set_of_subset_set_of],
    apply le_of_lt },

  -- F(-, x) is continuous at s-1, for almost all x
  have F_cts: ∀ᵐ (x : ℝ) ∂measure_space.volume.restrict (Ioi 0),
      continuous_at (λ (t : ℝ), exp (-x) * x ^ (t - 1) ) s,
  { have emp: {a : ℝ | ¬continuous_at (λ (t : ℝ), exp (-a) * a ^ (t - 1)) s} ∩ Ioi 0 = ∅,
    { ext,
      simp only [mem_inter_eq, mem_set_of_eq, set.mem_Ioi,
        mem_empty_eq, iff_false, not_and, not_lt],
      contrapose,
      simp only [not_le, not_not],
      intro hx,
      apply continuous_at.mul,
      { apply continuous_at_const },
      { apply continuous_at.rpow,
        apply continuous_at_const,
        apply continuous_at.sub,
        apply continuous_at_id,
        apply continuous_at_const,
        left, exact hx.ne'}, },
    rw ae_iff,
    rw measure.restrict_apply',
    { rw emp,
      exact measure_empty, },
    apply measurable_set_Ioi },

  apply continuous_at_of_dominated ae_meas bound bd_integrable F_cts,
end

lemma gamma_right_cts: continuous_within_at real_gamma (set.Ici (1:ℝ)) 1 :=
begin
  have s1: continuous_within_at (λ s:ℝ, real_gamma(s+1) / s) (set.Ici (1:ℝ)) 1,
  { apply continuous_at.continuous_within_at,
    refine (continuous_at.div _ continuous_at_id one_ne_zero),
    apply continuous_at.comp,
    { apply continuous_on.continuous_at (gamma_cts_Ioi) (Ioi_mem_nhds _),
      linarith, },
    { exact continuous_at.add continuous_at_id continuous_at_const, }, },

  refine (continuous_within_at.congr s1 _ (by {rw gamma_recurrence, simp })),
  intros y hy,
  rw [set.Ici, mem_set_of_eq] at hy,
  rw (gamma_recurrence _ hy),
  rw [mul_comm, mul_div_cancel],
  linarith,
end

lemma gamma_cts_Ici: continuous_on real_gamma (Ici 1):=
begin
  intros s hs,
  by_cases s ∈ Ioi (1:ℝ),
  { apply continuous_at.continuous_within_at,
    apply continuous_on.continuous_at gamma_cts_Ioi,
    apply Ioi_mem_nhds,
    rw [set.Ioi, mem_set_of_eq] at h, linarith,},
  { have : s = 1,
    { rw not_mem_Ioi at h, rw [set.Ici, mem_set_of_eq] at hs, linarith },
    rw this, exact gamma_right_cts, }
end

end real.gamma
