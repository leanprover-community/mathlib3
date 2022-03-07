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
definition `Γ(s) = ∫ x in 0..∞, x^(s-1) exp(-x) dx`, and prove that it satisfies the relation
`Γ(s+1) = s Γ(s)`. We also prove that `Γ(n+1) = n!` for `n ∈ ℕ`. We also show that `Γ(s)` is
continuous on `(1, ∞)` (but not yet at the left endpoint).

TO DO:

- Extend to the whole real line.
- Allow complex `s` and prove analyticity.

## Tags

gamma
-/

noncomputable theory
open finset filter metric interval_integral set function
open_locale classical topological_space ennreal filter measure_theory

namespace real

/- The integrand function and its properties -/

def F (s x : ℝ) : ℝ := exp(-x) * x^s

/- We prove some lemmas about F:

- for any `s ≥ 0`, F is continuous of `x ∈ [0,∞)`;
- for any `s ≥ 1`, the derivative of `F(s, -)` at any `x ∈ [0, ∞)` is what it should be;
- for any `s ≥ 1`, the derivative of `F(s, -)` is integrable on [0, X] for any X ≥ 0;
- for any `s ∈ ℝ`, F is `O( exp(-(1/2) * x))` as `x → ∞`.
-/

lemma cont_F (s : ℝ) (h1: 0 ≤ s) :
  continuous_on s.F (Ici 0) :=
begin
  apply continuous_on.mul,
  { apply continuous_on.exp,
    apply continuous_on.neg,
    apply continuous_on_id },
  { apply continuous_on.rpow_const,
    apply continuous_on_id,
    tauto }
end

lemma deriv_F (s x: ℝ) (h1: 1 ≤ s) (h2: 0 ≤ x) : has_deriv_at s.F
(- (exp (-x) * x ^ s) + exp (-x) * (s * x ^ (s - 1))) x :=
begin
  have d1 : has_deriv_at (λ (y: ℝ), exp(-y)) (-exp(-x)) x,
  { simpa using has_deriv_at.exp (has_deriv_at_neg x) },
  have d2 : has_deriv_at (λ (y: ℝ), y^s) (s*x^(s-1)) x,
  { apply has_deriv_at_rpow_const,
    right,
    exact h1 },
  simpa using has_deriv_at.mul d1 d2
end

lemma dF_interval_integrable (s X: ℝ) (hs: 1 ≤ s) (hX: 0 ≤ X):
interval_integrable (λ (x : ℝ),  -(exp (-x) * x ^ s) + exp (-x) * (s * x ^ (s - 1)))
  measure_theory.measure_space.volume 0 X :=
begin
  apply continuous_on.interval_integrable,

  have c : continuous_on (λ (x : ℝ), exp (-x)) (interval 0 X),
  { apply continuous_on.exp,
    apply continuous_on.neg,
    apply continuous_on_id },

  -- This is an awful mess,
  -- proving continuity of a function
  -- built up as a sum of many terms.
  apply continuous_on.add,
  apply continuous_on.neg,
  apply continuous_on.mul,
  exact c,
  apply continuous_on.rpow_const,
  apply continuous_at.continuous_on,
  intros x hxX,
  apply continuous_at_id,
  intros x hxX,
  right, linarith,

  -- halfway...
  apply continuous_on.mul,
  exact c,
  apply continuous_on.mul,
  { apply continuous.continuous_on,
  apply continuous_const },
  apply continuous_on.rpow_const,
  apply continuous_at.continuous_on,
  intros x hxX,
  apply continuous_at_id,
  intros x hxX,
  right, linarith,
end



/- A long and fiddly argument to show that F decays exponentially at +∞ -/


/- The next three lemmas should really be in exp.lean or somewhere like that -/
lemma tendsto_exp_div_rpow_at_top (s : ℝ) : tendsto (λ x : ℝ, exp x / x ^ s ) at_top at_top :=
begin
  have := archimedean_iff_nat_lt.1 (real.archimedean) s,
  cases this with n hn,
  have t := tendsto_exp_div_pow_at_top n,
  have : 0 < (n:ℝ) - s := by linarith,
  replace t := tendsto.at_top_mul_at_top t (tendsto_rpow_at_top this),

  let f1 := (λ x:ℝ, (exp x / x ^ n) * (x ^ (↑n - s))),
  let f2 := (λ x:ℝ, exp x / x ^ s),
  have ff1: f1 = (λ x:ℝ, (exp x / x ^ n) * (x ^ (↑n - s))) := by refl,
  have ff2: f2 = (λ x:ℝ, exp x / x ^ s) := by refl,

  have : ∀ x : ℝ, (0 < x) → f1 x = f2 x,
  { intros x h,
    rw [ff1,ff2],
    ring_nf,
    rw mul_eq_mul_right_iff,
    left,
    rw [sub_eq_neg_add,rpow_add_nat, mul_assoc],
    have : x^n * (x^n)⁻¹ = 1,
    apply mul_inv_cancel,
    apply pow_ne_zero,
    exact h.ne',
    rw [this, mul_one],
    apply rpow_neg,
    exact le_of_lt(h),
    exact h.ne' },

  have Icieq: eq_on f1 f2 (Ici 1),
  { intros x hx,
    rw [set.Ici, mem_set_of_eq] at hx,
    have b: 0 < x := by linarith,
    exact (this x b) },

  have eveq : eventually_eq at_top f1 f2,
  { rw eventually_eq_iff_exists_mem,
    use (Ici 1),
    split,
    apply mem_at_top,
    exact Icieq },
  apply tendsto.congr' eveq,
  exact t,
end

/- This one too -- a more general version allowing exp(-bx) for any b > 0 -/
lemma tendsto_exp_mul_div_rpow_at_top (s : ℝ) (b : ℝ) (hb : 0 < b):
  tendsto (λ x : ℝ, exp (b * x) / x ^ s ) at_top at_top :=
begin
  have t1 := tendsto_exp_div_rpow_at_top (s/b),
  have t2 := tendsto_rpow_at_top hb,
  have t := tendsto.comp t2 t1,

  let f1 := (λ (x : ℝ), (exp x / x ^ (s / b)) ^ b),
  let f2 := (λ x : ℝ, exp (b * x) / x ^ s ),
  have ff1 : ∀ x:ℝ, f1 x = (exp x / x ^ (s / b)) ^ b,
  { by simp only [eq_self_iff_true, forall_const] },
  have ff2 : ∀ x:ℝ, f2 x = exp (b * x) / x ^ s,
  {by simp only [eq_self_iff_true, forall_const] },

  have Ioieq: eq_on f1 f2 (Ioi 0),
  { intros x hx,
    rw [set.Ioi, mem_set_of_eq] at hx,
    rw [ff1, ff2],
    rw div_rpow,
    -- clean up the subgoals introduced by div_rpow
    show 0 ≤ exp x,
    { apply le_of_lt(exp_pos x) },
    show 0 ≤ x ^ (s / b),
    { apply le_of_lt,
      apply rpow_pos_of_pos hx },

    have : exp x ^ b = exp (b * x),
    { calc exp x ^ b = exp(log (exp x ^ b ) ) : by { rw exp_log, apply rpow_pos_of_pos (exp_pos x) }
      ...            = exp( b * log (exp x) ) : by rw log_rpow (exp_pos x)
      ...            = exp( b * x )           : by rw log_exp },
    rw this,
    rw div_eq_div_iff,
    show x^s ≠ 0,
    { symmetry, apply ne_of_lt,
      apply rpow_pos_of_pos,
      linarith },
    show (x ^ (s / b)) ^ b ≠ 0,
    { symmetry, apply ne_of_lt,
      apply rpow_pos_of_pos,
      apply rpow_pos_of_pos,
      linarith },
    rw mul_eq_mul_left_iff,
    left,
    rw ←rpow_mul,
    show 0 ≤ x, linarith,
    rw div_mul_cancel, exact hb.ne' },
  have : Ici (1:ℝ) ⊆ Ioi (0:ℝ),
  { rw [set.Ioi, set.Ici],
    intro x,
    rw mem_set_of_eq,rw mem_set_of_eq,
    intro hx,linarith },
  have Ioi_at_top: Ioi (0:ℝ) ∈ at_top := Ioi_mem_at_top (0:ℝ),
  have ev_eq: eventually_eq at_top f1 f2 := eventually_eq_of_mem Ioi_at_top Ioieq,

  exact tendsto.congr' ev_eq t
end

lemma tendsto_exp_mul_div_rpow_at_top' (s : ℝ) (b : ℝ) (hb : 0 < b):
  tendsto (λ x : ℝ, x^s * exp (-b * x)) at_top (𝓝 $ (0:ℝ)) :=
begin
  have l := tendsto_exp_mul_div_rpow_at_top s b hb,
  have:  (λ x : ℝ, x^s * exp (-b * x)) =  (λ x : ℝ, exp (b * x) / x^s)⁻¹,
  { ext,
    simp only [neg_mul, pi.inv_apply],
    rw [inv_div,div_eq_mul_inv],
    rw mul_eq_mul_left_iff,
    left,
    apply exp_neg },
  rw this,
  exact tendsto.inv_tendsto_at_top l
end

/- Now we have the bits we need -/
lemma asymp_F (s : ℝ) :
  asymptotics.is_O s.F (λ x : ℝ, exp(-(1/2) * x)) filter.at_top :=
begin
  apply asymptotics.is_o.is_O,
  apply asymptotics.is_o_of_tendsto,
  { intros x hx,
    exfalso,
    apply ( exp_pos(-(1/2) * x)).ne',
    exact hx },
  simp only [F],

  have : ∀ (x: ℝ), (x > 0) → (exp (-x) * x ^ s / exp (-(1 / 2) * x) = exp (-(1/2) * x) * x ^ s),
  { intros x h,
    rw mul_comm,
    rw mul_comm (exp (-(1/2) * x)) (x ^ s),
    rw div_eq_of_eq_mul,
    exact (exp_pos (-(1/2) * x)).ne',
    have: exp(-x) = exp(-(1/2)*x) * exp (-(1 / 2) * x),
    { rw ←real.exp_add,
      simp only [exp_eq_exp],
      ring },
    rw this,
    ring },
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
  exact (tendsto_exp_mul_div_rpow_at_top s (1/2))(one_half_pos) -- hooray!
end

lemma loc_unif_bound_F (s : ℝ) (h: 0 < s) (t: ℝ) (ht: t ∈ set.Icc 0 s )
  (x:ℝ) (hx: x ∈ set.Ioi (0:ℝ)): F t x ≤  F s x + F 0 x:=
begin
  rw [set.Ioi,mem_set_of_eq] at hx,
  rw [set.Icc,mem_set_of_eq] at ht,
  by_cases (1 ≤ x),
  { suffices: F t x ≤ F s x, -- case 1 ≤ x
    { suffices: 0 ≤ F 0 x,
      { linarith },
      simp only [F, rpow_zero, mul_one],
      exact le_of_lt(exp_pos (-x)) },
    simp only [F],
    apply mul_le_mul,
    refl,
    apply rpow_le_rpow_of_exponent_le h ht.2,
    apply le_of_lt,
    apply rpow_pos_of_pos,
    linarith,
    exact le_of_lt(exp_pos (-x)) },
  { simp only [not_le] at h, -- case x < 1
    suffices: F t x ≤ F 0 x,
    { suffices: 0 ≤ F s x,
      { linarith },
      apply le_of_lt,
      apply mul_pos,
      apply exp_pos,
      apply rpow_pos_of_pos hx },
    simp only [F],
    rw [rpow_zero, mul_one],
    rw mul_le_iff_le_one_right,
    apply rpow_le_one,
    exact le_of_lt hx,
    exact le_of_lt h,
    exact ht.1,
    exact exp_pos (-x) },
end


/- The lower incomplete Γ function. This is an object of independent interest, so we
prove the recurrence in terms of incomplete Γ and deduce it for the genuine Γ later. -/

def real_incomplete_gamma (s X : ℝ) : ℝ := ∫ x in 0..X, exp(-x) * x^(s-1)

lemma gamma_FE_incomp (s X : ℝ) (h: 1 ≤ s) (h2: 0 ≤ X):
  real_incomplete_gamma (s+1) X = s * real_incomplete_gamma s X - X^s * exp(-X) :=
begin
  rw real_incomplete_gamma,
  rw real_incomplete_gamma,

  have F_der_I: (∀ (x:ℝ), (x ∈ interval 0 X) →
    has_deriv_at s.F (- (exp (-x) * x ^ s) + exp (-x) * (s * x ^ (s - 1))) x),
  { intros x hx,
    cases hx,
    rw min_def at hx_left,
    split_ifs at hx_left,
    exact deriv_F s x h hx_left,
    tauto },

  have int_eval := integral_eq_sub_of_has_deriv_at F_der_I (dF_interval_integrable s X h h2),

  have : (F s 0) = 0,
  { rw F, rw zero_rpow, ring, apply ne_of_gt,
    apply lt_of_lt_of_le zero_lt_one h },
  rw [this, F] at int_eval,
  simp only [sub_zero] at int_eval,
  rw integral_add at int_eval,
  { simp only [add_tsub_cancel_right],
    have : (∫ (x : ℝ) in 0..X, exp (-x) * x ^ s)
      = (∫ (x : ℝ) in 0..X, exp (-x) * (s * x ^ (s - 1))) - exp (-X) * X ^ s,
    { rw sub_eq_neg_add,
      apply eq_add_of_add_neg_eq,
      rw ← int_eval,
      simp only [integral_neg, neg_add_rev, neg_neg], ring },
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
    have := cont_F s (le_trans zero_le_one h),
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

lemma integrable_F (s: ℝ) (h: 1 ≤ s): measure_theory.integrable_on
  (λ (x:ℝ), exp(-x) * x^(s-1)) (Ioi 0) :=
begin
  apply limit_comparison.integrable_bigoh_exp (s-1).F 0 one_half_pos,
  apply cont_F,
  { linarith },
  exact asymp_F (s-1)
end

def real_gamma (s: ℝ) : ℝ :=  ∫ x in (Ioi 0), exp(-x) * x^(s-1)

lemma tendsto_incomplete_gamma (s : ℝ) (h: 1 ≤ s):
  tendsto (s.real_incomplete_gamma) (filter.at_top)  (𝓝 $ real_gamma s) :=
begin
  apply measure_theory.interval_integral_tendsto_integral_Ioi,
  swap, apply tendsto_id,
  exact integrable_F s h
end

lemma FE_gamma (s : ℝ) (h: 1 ≤ s) :
  real_gamma (s+1) = s * real_gamma s :=
begin
  have t1: tendsto (s+1).real_incomplete_gamma at_top (𝓝 (s+1).real_gamma),
  { apply tendsto_incomplete_gamma, linarith },
  suffices t2: tendsto (s+1).real_incomplete_gamma at_top (𝓝 $ s * real_gamma s),
  { apply tendsto_nhds_unique t1 t2 },

  have a: eventually_eq at_top ((s+1).real_incomplete_gamma)
    (λ X:ℝ, s * real_incomplete_gamma s X - X^s * exp(-X)),
  { apply eventually_eq_of_mem (Ici_mem_at_top (0:ℝ)),
    intros X hX,
    rw [set.Ici, mem_set_of_eq] at hX,
    exact gamma_FE_incomp s X h hX },
  replace a := eventually_eq.symm a,

  suffices b: tendsto (λ X:ℝ, s * real_incomplete_gamma s X - X^s * exp(-X)) at_top
    (𝓝 $ s * real_gamma s),
  { exact tendsto.congr' a b, },

  have l1: tendsto (λ X:ℝ, s * real_incomplete_gamma s X) at_top (𝓝 $ s * real_gamma s),
  { apply tendsto.const_mul,
    exact tendsto_incomplete_gamma s h },
  suffices l2: tendsto (λ X:ℝ, -X^s * exp(-X)) at_top (𝓝 $ (0:ℝ)),
  { have := tendsto.add l1 l2,
    simpa using this },
  have l3: tendsto (λ X:ℝ, X^s * exp(-X)) at_top (𝓝 $ (0:ℝ)),
  { have := tendsto_exp_mul_div_rpow_at_top' s (1:ℝ) zero_lt_one,
    simpa using this },
  have: (λ X:ℝ, -X^s * exp(-X)) = (λ X:ℝ, (-1) * (X^s * exp(-X))) :=
    by { simp only [neg_mul, one_mul] },
  rw this,
  have : (0:ℝ) = (-1) * (0:ℝ) := by {ring, },
  rw this,
  apply tendsto.const_mul,
  exact l3
end

lemma incomp_gamma_at_one (X : ℝ) (hX: 0 < X): real_incomplete_gamma 1 X = 1-exp(-X) :=
begin
  rw real_incomplete_gamma,
  simp
end

lemma gamma_at_one: real_gamma 1 = 1 :=
begin
  have t1: tendsto (1:ℝ).real_incomplete_gamma at_top (𝓝 (1:ℝ).real_gamma),
  { apply tendsto_incomplete_gamma,
    refl },
  have t2: tendsto (1:ℝ).real_incomplete_gamma at_top (𝓝 (1:ℝ)),
  { have t2a: eventually_eq at_top (λ X:ℝ, 1-exp(-X)) (1:ℝ).real_incomplete_gamma,
    { apply eventually_eq_of_mem (Ioi_mem_at_top (0:ℝ)),
      intros X hX,
      symmetry,
      apply incomp_gamma_at_one,
      rw [←Ioi_def, mem_set_of_eq] at hX, exact hX },
    apply tendsto.congr' t2a,

    have t2b: tendsto (λ X, exp(-X)) at_top (𝓝 (0:ℝ)),
    { have := tendsto_exp_mul_div_rpow_at_top' 0 1,
      simpa using this },
    have := tendsto.const_sub (1:ℝ) t2b,
    simpa using this },
  apply tendsto_nhds_unique t1 t2
end

lemma gamma_integer: ∀ n:ℕ, real_gamma (n+1) = nat.factorial n :=
begin
  intro n,
  induction n with n hn,

  simp only [nat.cast_zero, zero_add, nat.factorial_zero, nat.cast_one],
  exact gamma_at_one,

  rw FE_gamma,
  simp only [nat.cast_succ, nat.factorial_succ, nat.cast_mul, mul_eq_mul_left_iff],
  left, exact hn,

  simp only [nat.cast_succ, le_add_iff_nonneg_left, nat.cast_nonneg]
end


/- Continuity of the gamma function. This is proved using `continuous_at_of_dominated`, so
we need to verify the hypotheses. -/
lemma gamma_cts: continuous_on real_gamma (Ioi 1):=
begin

  apply continuous_at.continuous_on,
  intros s hs,
  rw [set.Ioi, mem_set_of_eq] at hs,

  have Ioo_nhd: Ioo 1 (s+1) ∈ 𝓝 s,
  { apply Ioo_mem_nhds,
    linarith, linarith },

  -- F(t-1, -) is bounded, locally uniformly in t near s
  have bound: ∀ᶠ (t : ℝ) in 𝓝 s, ∀ᵐ (x : ℝ) ∂ measure_theory.measure_space.volume.restrict (Ioi 0),
    ∥exp (-x) * x ^ (t - 1)∥ ≤ (λ y:ℝ, F s y + F 0 y) x,
  { apply eventually_of_mem (Ioo_nhd),
    intros t ht,
    rw [set.Ioo, mem_set_of_eq] at ht,

    rw measure_theory.ae_iff,
    rw measure_theory.measure.restrict_apply',
    swap, apply measurable_set_Ioi,
    suffices: ({a : ℝ | ¬∥exp (-a) * a ^ (t - 1)∥ ≤ (λ (y : ℝ), F s y + F 0 y) a} ∩ Ioi 0)
      = ∅,
    { rw this,
      apply measure_theory.measure_empty },
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
    have: exp(-x) * x^(t-1) ≤ F s x + F 0 x,
    { apply loc_unif_bound_F s _ (t-1),
      rw [set.Icc,mem_set_of_eq],
      split,
      linarith,linarith,
      tauto,linarith },
    exact this },

  -- The upper bound is integrable
  have bd_integrable: measure_theory.integrable (λ (x : ℝ), F s x + F 0 x)
  (measure_theory.measure_space.volume.restrict (Ioi 0)),
  { apply measure_theory.integrable.add,
    { have: 1 ≤ s+1,
      { linarith },
      replace := integrable_F (s+1) this,
      simpa using this },
    { have := integrable_F (1:ℝ) (le_refl (1:ℝ)),
      rw sub_self at this,
      exact this } },

  -- F(t-1, -) is a.e. measurable in x, for all t near s
  have ae_meas: ∀ᶠ (t : ℝ) in 𝓝 s, ae_measurable (λ (x : ℝ), exp (-x) * x ^ (t - 1))
    (measure_theory.measure_space.volume.restrict (Ioi 0)),
  { apply eventually_of_mem (Ioi_mem_nhds hs),
    intros t ht,
    rw [set.Ioi, mem_set_of_eq] at ht,
    apply continuous_on.ae_measurable,
    have : 0 ≤ t-1 := by linarith,
    replace := (cont_F (t-1) this),

    apply continuous_on.mono this,
    rw [set.Ioi, set.Ici, set_of_subset_set_of],
    intro a,
    apply le_of_lt,
    apply measurable_set_Ioi },

  -- F(-, x) is continuous at s-1, for almost all x
  have F_cts: ∀ᵐ (x : ℝ) ∂measure_theory.measure_space.volume.restrict (Ioi 0),
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
    rw measure_theory.ae_iff,
    rw measure_theory.measure.restrict_apply',
    rw emp,
    exact measure_theory.measure_empty,
    apply measurable_set_Ioi },

  apply measure_theory.continuous_at_of_dominated ae_meas bound bd_integrable F_cts,
end

end real
