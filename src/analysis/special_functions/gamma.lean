/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import measure_theory.integral.exp_decay
import analysis.calculus.parametric_integral

/-!
# The Gamma function

This file defines the `Γ` function (of a real or complex variable `s`). We define this by Euler's
integral `Γ(s) = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1)` in the range where this integral converges
(i.e., for `0 < s` in the real case, and `0 < re s` in the complex case).

We show that this integral satisfies `Γ(1) = 1` and `Γ(s + 1) = s * Γ(s)`; hence we can define
`Γ(s)` for all `s` as the unique function satisfying this recurrence and agreeing with Euler's
integral in the convergence range. In the complex case we also prove that the resulting function is
holomorphic on `ℂ` away from the points `{-n : n ∈ ℤ}`.

## Tags

Gamma
-/

noncomputable theory
open filter interval_integral set real measure_theory asymptotics
open_locale topological_space

lemma integral_exp_neg_Ioi : ∫ (x : ℝ) in Ioi 0, exp (-x) = 1 :=
begin
  refine tendsto_nhds_unique (interval_integral_tendsto_integral_Ioi _ _ tendsto_id) _,
  { simpa only [neg_mul, one_mul] using exp_neg_integrable_on_Ioi 0 zero_lt_one, },
  { simpa using tendsto_exp_neg_at_top_nhds_0.const_sub 1, },
end

namespace real

/-- Asymptotic bound for the `Γ` function integrand. -/
lemma Gamma_integrand_is_o (s : ℝ) :
  (λ x:ℝ, exp (-x) * x ^ s) =o[at_top] (λ x:ℝ, exp (-(1/2) * x)) :=
begin
  refine is_o_of_tendsto (λ x hx, _) _,
  { exfalso, exact (exp_pos (-(1 / 2) * x)).ne' hx },
  have : (λ (x:ℝ), exp (-x) * x ^ s / exp (-(1 / 2) * x)) = (λ (x:ℝ), exp ((1 / 2) * x) / x ^ s )⁻¹,
  { ext1 x,
    field_simp [exp_ne_zero, exp_neg, ← real.exp_add],
    left,
    ring },
  rw this,
  exact (tendsto_exp_mul_div_rpow_at_top s (1 / 2) one_half_pos).inv_tendsto_at_top,
end

/-- Euler's integral for the `Γ` function (of a real variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `Gamma_integral_convergent` for a proof of the convergence of the integral for `0 < s`. -/
def Gamma_integral (s : ℝ) : ℝ := ∫ x in Ioi (0:ℝ), exp (-x) * x ^ (s - 1)

/-- The integral defining the `Γ` function converges for positive real `s`. -/
lemma Gamma_integral_convergent {s : ℝ} (h : 0 < s) :
  integrable_on (λ x:ℝ, exp (-x) * x ^ (s - 1)) (Ioi 0) :=
begin
  rw [←Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrable_on_union],
  split,
  { rw ←integrable_on_Icc_iff_integrable_on_Ioc,
    refine integrable_on.continuous_on_mul continuous_on_id.neg.exp _ is_compact_Icc,
    refine (interval_integrable_iff_integrable_Icc_of_le zero_le_one).mp _,
    exact interval_integrable_rpow' (by linarith), },
  { refine integrable_of_is_O_exp_neg one_half_pos _ (Gamma_integrand_is_o _ ).is_O,
    refine continuous_on_id.neg.exp.mul (continuous_on_id.rpow_const _),
    intros x hx,
    exact or.inl ((zero_lt_one : (0 : ℝ) < 1).trans_le hx).ne' }
end

lemma Gamma_integral_one : Gamma_integral 1 = 1 :=
by simpa only [Gamma_integral, sub_self, rpow_zero, mul_one] using integral_exp_neg_Ioi

end real

namespace complex
/- Technical note: In defining the Gamma integrand exp (-x) * x ^ (s - 1) for s complex, we have to
make a choice between ↑(real.exp (-x)), complex.exp (↑(-x)), and complex.exp (-↑x), all of which are
equal but not definitionally so. We use the first of these throughout. -/


/-- The integral defining the `Γ` function converges for complex `s` with `0 < re s`.

This is proved by reduction to the real case. -/
lemma Gamma_integral_convergent {s : ℂ} (hs : 0 < s.re) :
  integrable_on (λ x, (-x).exp * x ^ (s - 1) : ℝ → ℂ) (Ioi 0) :=
begin
  split,
  { refine continuous_on.ae_strongly_measurable _ measurable_set_Ioi,
    apply (continuous_of_real.comp continuous_neg.exp).continuous_on.mul,
    apply continuous_at.continuous_on,
    intros x hx,
    have : continuous_at (λ x:ℂ, x ^ (s - 1)) ↑x,
    { apply continuous_at_cpow_const, rw of_real_re, exact or.inl hx, },
    exact continuous_at.comp this continuous_of_real.continuous_at },
  { rw ←has_finite_integral_norm_iff,
    refine has_finite_integral.congr (real.Gamma_integral_convergent hs).2 _,
    refine (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ (λ x hx, _)),
    dsimp only,
    rw [norm_eq_abs, abs_mul, abs_of_nonneg $ le_of_lt $ exp_pos $ -x,
      abs_cpow_eq_rpow_re_of_pos hx _],
    simv }
end

/-- Euler's integral for the `Γ` function (of a complex variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `complex.Gamma_integral_convergent` for a proof of the convergence of the integral for
`0 < re s`. -/
def Gamma_integral (s : ℂ) : ℂ := ∫ x in Ioi (0:ℝ), ↑(-x).exp * ↑x ^ (s - 1)

lemma Gamma_integral_of_real (s : ℝ) :
  Gamma_integral ↑s = ↑(s.Gamma_integral) :=
begin
  rw [real.Gamma_integral, ←integral_of_real],
  refine set_integral_congr measurable_set_Ioi _,
  intros x hx, dsimp only,
  rw [of_real_mul, of_real_cpow (mem_Ioi.mp hx).le],
  simv,
end

lemma Gamma_integral_one : Gamma_integral 1 = 1 :=
begin
  rw [←of_real_one, Gamma_integral_of_real, of_real_inj],
  exact real.Gamma_integral_one,
end

end complex

/-! Now we establish the recurrence relation `Γ(s + 1) = s * Γ(s)` using integration by parts. -/

namespace complex

section Gamma_recurrence

/-- The indefinite version of the `Γ` function, `Γ(s, X) = ∫ x ∈ 0..X, exp(-x) x ^ (s - 1)`. -/
def partial_Gamma (s : ℂ) (X : ℝ) : ℂ := ∫ x in 0..X, (-x).exp * x ^ (s - 1)

lemma tendsto_partial_Gamma {s : ℂ} (hs: 0 < s.re) :
  tendsto (λ X:ℝ, partial_Gamma s X) at_top (𝓝 $ Gamma_integral s) :=
interval_integral_tendsto_integral_Ioi 0 (Gamma_integral_convergent hs) tendsto_id

private lemma Gamma_integrand_interval_integrable (s : ℂ) {X : ℝ} (hs : 0 < s.re) (hX : 0 ≤ X):
  interval_integrable (λ x, (-x).exp * x ^ (s - 1) : ℝ → ℂ) volume 0 X :=
begin
  rw interval_integrable_iff_integrable_Ioc_of_le hX,
  exact integrable_on.mono_set (Gamma_integral_convergent hs) Ioc_subset_Ioi_self
end

private lemma Gamma_integrand_deriv_integrable_A {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 0 ≤ X):
 interval_integrable (λ x, -((-x).exp * x ^ s) : ℝ → ℂ) volume 0 X :=
begin
  convert (Gamma_integrand_interval_integrable (s+1) _ hX).neg,
  { ext1, simv only [add_sub_cancel, pi.neg_apply] },
  { simv only [add_re, one_re], linarith,},
end

private lemma Gamma_integrand_deriv_integrable_B {s : ℂ} (hs : 0 < s.re) {Y : ℝ} (hY : 0 ≤ Y) :
  interval_integrable (λ (x : ℝ), (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) volume 0 Y :=
begin
  have : (λ x, (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) =
    (λ x, s * ((-x).exp * x ^ (s - 1)) : ℝ → ℂ),
  { ext1, ring, },
  rw [this, interval_integrable_iff_integrable_Ioc_of_le hY],
  split,
  { refine (continuous_on_const.mul _).ae_strongly_measurable measurable_set_Ioc,
    apply (continuous_of_real.comp continuous_neg.exp).continuous_on.mul,
    apply continuous_at.continuous_on,
    intros x hx,
    refine (_ : continuous_at (λ x:ℂ, x ^ (s - 1)) _).comp continuous_of_real.continuous_at,
    apply continuous_at_cpow_const, rw of_real_re, exact or.inl hx.1, },
  rw ←has_finite_integral_norm_iff,
  simp_rw [norm_eq_abs, complex.abs_mul],
  refine (((real.Gamma_integral_convergent hs).mono_set
    Ioc_subset_Ioi_self).has_finite_integral.congr _).const_mul _,
  rw [eventually_eq, ae_restrict_iff'],
  { apply ae_of_all, intros x hx,
    rw [abs_of_nonneg (exp_pos _).le,abs_cpow_eq_rpow_re_of_pos hx.1],
    simv },
  { exact measurable_set_Ioc},
end

/-- The recurrence relation for the indefinite version of the `Γ` function. -/
lemma partial_Gamma_add_one {s : ℂ} (hs: 0 < s.re) {X : ℝ} (hX : 0 ≤ X) :
  partial_Gamma (s + 1) X = s * partial_Gamma s X - (-X).exp * X ^ s :=
begin
  rw [partial_Gamma, partial_Gamma, add_sub_cancel],
  have F_der_I: (∀ (x:ℝ), (x ∈ Ioo 0 X) → has_deriv_at (λ x, (-x).exp * x ^ s : ℝ → ℂ)
    ( -((-x).exp * x ^ s) + (-x).exp * (s * x ^ (s - 1))) x),
  { intros x hx,
    have d1 : has_deriv_at (λ (y: ℝ), (-y).exp) (-(-x).exp) x,
    { simpa using (has_deriv_at_neg x).exp },
    have d1b : has_deriv_at (λ y, ↑(-y).exp : ℝ → ℂ) (↑-(-x).exp) x,
    { convert has_deriv_at.scomp x of_real_clm.has_deriv_at d1, simv, },
    have d2: has_deriv_at (λ (y : ℝ), ↑y ^ s) (s * x ^ (s - 1)) x,
    { have t := @has_deriv_at.cpow_const _ _ _ s (has_deriv_at_id ↑x),
      simv only [id.def, of_real_re, of_real_im,
        ne.def, eq_self_iff_true, not_true, or_false, mul_one] at t,
      simpa using has_deriv_at.comp x (t hx.left) of_real_clm.has_deriv_at, },
    simpa only [of_real_neg, neg_mul] using d1b.mul d2 },
  have cont := (continuous_of_real.comp continuous_neg.exp).mul
    (continuous_of_real_cpow_const hs),
  have der_ible := (Gamma_integrand_deriv_integrable_A hs hX).add
    (Gamma_integrand_deriv_integrable_B hs hX),
  have int_eval := integral_eq_sub_of_has_deriv_at_of_le hX cont.continuous_on F_der_I der_ible,
  -- We are basically done here but manipulating the output into the right form is fiddly.
  apply_fun (λ x:ℂ, -x) at int_eval,
  rw [interval_integral.integral_add (Gamma_integrand_deriv_integrable_A hs hX)
    (Gamma_integrand_deriv_integrable_B hs hX), interval_integral.integral_neg, neg_add, neg_neg]
    at int_eval,
  replace int_eval := eq_sub_of_add_eq int_eval,
  rw [int_eval, sub_neg_eq_add, neg_sub, add_comm, add_sub],
  simv only [sub_left_inj, add_left_inj],
  have : (λ x, (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) = (λ x, s * (-x).exp * x ^ (s - 1) : ℝ → ℂ),
  { ext1, ring,},
  rw this,
  have t := @integral_const_mul (0:ℝ) X volume _ _ s (λ x:ℝ, (-x).exp * x ^ (s - 1)),
  dsimp at t, rw [←t, of_real_zero, zero_cpow],
  { rw [mul_zero, add_zero], congr', ext1, ring },
  { contrapose! hs, rw [hs, zero_re] }
end

/-- The recurrence relation for the `Γ` integral. -/
theorem Gamma_integral_add_one {s : ℂ} (hs: 0 < s.re) :
  Gamma_integral (s + 1) = s * Gamma_integral s :=
begin
  suffices : tendsto (s+1).partial_Gamma at_top (𝓝 $ s * Gamma_integral s),
  { refine tendsto_nhds_unique _ this,
    apply tendsto_partial_Gamma, rw [add_re, one_re], linarith, },
  have : (λ X:ℝ, s * partial_Gamma s X - X ^ s * (-X).exp) =ᶠ[at_top] (s+1).partial_Gamma,
  { apply eventually_eq_of_mem (Ici_mem_at_top (0:ℝ)),
    intros X hX,
    rw partial_Gamma_add_one hs (mem_Ici.mp hX),
    ring_nf, },
  refine tendsto.congr' this _,
  suffices : tendsto (λ X, -X ^ s * (-X).exp : ℝ → ℂ) at_top (𝓝 0),
  { simpa using tendsto.add (tendsto.const_mul s (tendsto_partial_Gamma hs)) this },
  rw tendsto_zero_iff_norm_tendsto_zero,
  have : (λ (e : ℝ), ∥-(e:ℂ) ^ s * (-e).exp∥ ) =ᶠ[at_top] (λ (e : ℝ), e ^ s.re * (-1 * e).exp ),
  { refine eventually_eq_of_mem (Ioi_mem_at_top 0) _,
    intros x hx, dsimp only,
    rw [norm_eq_abs, abs_mul, abs_neg, abs_cpow_eq_rpow_re_of_pos hx,
      abs_of_nonneg (exp_pos(-x)).le, neg_mul, one_mul],},
  exact (tendsto_congr' this).mpr (tendsto_rpow_mul_exp_neg_mul_at_top_nhds_0 _ _ zero_lt_one),
end

end Gamma_recurrence

/-! Now we define `Γ(s)` on the whole complex plane, by recursion. -/

section Gamma_def

/-- The `n`th function in this family is `Γ(s)` if `-n < s.re`, and junk otherwise. -/
noncomputable def Gamma_aux : ℕ → (ℂ → ℂ)
| 0      := Gamma_integral
| (n+1)  := λ s:ℂ, (Gamma_aux n (s+1)) / s

lemma Gamma_aux_recurrence1 (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) :
  Gamma_aux n s = Gamma_aux n (s+1) / s :=
begin
  induction n with n hn generalizing s,
  { simv only [nat.cast_zero, neg_lt_zero] at h1,
    dsimp only [Gamma_aux], rw Gamma_integral_add_one h1,
    rw [mul_comm, mul_div_cancel], contrapose! h1, rw h1,
    simv },
  { dsimp only [Gamma_aux],
    have hh1 : -(s+1).re < n,
    { rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one] at h1,
      rw [add_re, one_re], linarith, },
    rw ←(hn (s+1) hh1) }
end

lemma Gamma_aux_recurrence2 (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) :
  Gamma_aux n s = Gamma_aux (n+1) s :=
begin
  cases n,
  { simv only [nat.cast_zero, neg_lt_zero] at h1,
    dsimp only [Gamma_aux],
    rw [Gamma_integral_add_one h1, mul_div_cancel_left],
    rintro rfl,
    rw [zero_re] at h1,
    exact h1.false },
  { dsimp only [Gamma_aux],
    have : (Gamma_aux n (s + 1 + 1)) / (s+1) = Gamma_aux n (s + 1),
    { have hh1 : -(s+1).re < n,
      { rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one] at h1,
        rw [add_re, one_re], linarith, },
      rw Gamma_aux_recurrence1 (s+1) n hh1, },
    rw this },
end


/-- The `Γ` function (of a complex variable `s`). -/
def Gamma (s : ℂ) : ℂ := Gamma_aux ⌊1 - s.re⌋₊ s

lemma Gamma_eq_Gamma_aux (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) : Gamma s = Gamma_aux n s :=
begin
  have u : ∀ (k : ℕ), Gamma_aux (⌊1 - s.re⌋₊ + k) s = Gamma s,
  { intro k, induction k with k hk,
    { simv [Gamma],},
    { rw [←hk, nat.succ_eq_add_one, ←add_assoc],
      refine (Gamma_aux_recurrence2 s (⌊1 - s.re⌋₊ + k) _).symm,
      rw nat.cast_add,
      have i0 := nat.sub_one_lt_floor (1 - s.re),
      simv only [sub_sub_cancel_left] at i0,
      refine lt_add_of_lt_of_nonneg i0 _,
      rw [←nat.cast_zero, nat.cast_le], exact nat.zero_le k, } },
  convert (u $ n - ⌊1 - s.re⌋₊).symm, rw nat.add_sub_of_le,
  by_cases (0 ≤ 1 - s.re),
  { apply nat.le_of_lt_succ,
    exact_mod_cast lt_of_le_of_lt (nat.floor_le h) (by linarith : 1 - s.re < n + 1) },
  { rw nat.floor_of_nonpos, linarith, linarith },
end

/-- The recurrence relation for the `Γ` function. -/
theorem Gamma_add_one (s : ℂ) (h2 : s ≠ 0) : Gamma (s+1) = s * Gamma s :=
begin
  let n := ⌊1 - s.re⌋₊,
  have t1 : -s.re < n,
  { simpa only [sub_sub_cancel_left] using nat.sub_one_lt_floor (1 - s.re) },
  have t2 : -(s+1).re < n,
  { rw [add_re, one_re], linarith, },
  rw [Gamma_eq_Gamma_aux s n t1, Gamma_eq_Gamma_aux (s+1) n t2, Gamma_aux_recurrence1 s n t1],
  field_simp, ring,
end

theorem Gamma_eq_integral (s : ℂ) (hs : 0 < s.re) : Gamma s = Gamma_integral s :=
Gamma_eq_Gamma_aux s 0 (by { norm_cast, linarith })

theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n+1) = nat.factorial n :=
begin
  induction n with n hn,
  { rw [nat.cast_zero, zero_add], rw Gamma_eq_integral,
    simpa using Gamma_integral_one, simv,},
  rw (Gamma_add_one n.succ $ nat.cast_ne_zero.mpr $ nat.succ_ne_zero n),
  { simv only [nat.cast_succ, nat.factorial_succ, nat.cast_mul], congr, exact hn },
end

end Gamma_def

end complex

/-! Now check that the `Γ` function is differentiable, wherever this makes sense. -/

section Gamma_has_deriv

/-- Integrand for the derivative of the `Γ` function -/
def dGamma_integrand (s : ℂ) (x : ℝ) : ℂ := exp (-x) * log x * x ^ (s - 1)

/-- Integrand for the absolute value of the derivative of the `Γ` function -/
def dGamma_integrand_real (s x : ℝ) : ℝ := |exp (-x) * log x * x ^ (s - 1)|

lemma dGamma_integrand_is_o_at_top (s : ℝ) :
  (λ x : ℝ, exp (-x) * log x * x ^ (s - 1)) =o[at_top] (λ x, exp (-(1/2) * x)) :=
begin
  refine is_o_of_tendsto (λ x hx, _) _,
  { exfalso, exact (-(1/2) * x).exp_pos.ne' hx, },
  have : eventually_eq at_top (λ (x : ℝ), exp (-x) * log x * x ^ (s - 1) / exp (-(1 / 2) * x))
    (λ (x : ℝ),  (λ z:ℝ, exp (1 / 2 * z) / z ^ s) x * (λ z:ℝ, z / log z) x)⁻¹,
  { refine eventually_of_mem (Ioi_mem_at_top 1) _,
    intros x hx, dsimp,
    replace hx := lt_trans zero_lt_one (mem_Ioi.mp hx),
    rw [real.exp_neg, neg_mul, real.exp_neg, rpow_sub hx],
    have : exp x = exp(x/2) * exp(x/2),
    { rw [←real.exp_add, add_halves], },
    rw this, field_simp [hx.ne', exp_ne_zero (x/2)], ring, },
  refine tendsto.congr' this.symm (tendsto.inv_tendsto_at_top _),
  apply tendsto.at_top_mul_at_top (tendsto_exp_mul_div_rpow_at_top s (1/2) one_half_pos),
  refine tendsto.congr' _ ((tendsto_exp_div_pow_at_top 1).comp tendsto_log_at_top),
  apply eventually_eq_of_mem (Ioi_mem_at_top (0:ℝ)),
  intros x hx, simv [exp_log hx],
end

/-- Absolute convergence of the integral which will give the derivative of the `Γ` function on
`1 < re s`. -/
lemma dGamma_integral_abs_convergent (s : ℝ) (hs : 1 < s) :
  integrable_on (λ x:ℝ, ∥exp (-x) * log x * x ^ (s-1)∥) (Ioi 0) :=
begin
  rw [←Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrable_on_union],
  refine ⟨⟨_, _⟩, _⟩,
  { refine continuous_on.ae_strongly_measurable (continuous_on.mul _ _).norm measurable_set_Ioc,
    { refine (continuous_exp.comp continuous_neg).continuous_on.mul (continuous_on_log.mono _),
      simv, },
    { apply continuous_on_id.rpow_const, intros x hx, right, linarith }, },
  { apply has_finite_integral_of_bounded,
    swap, { exact 1 / (s - 1), },
    refine (ae_restrict_iff' measurable_set_Ioc).mpr (ae_of_all _ (λ x hx, _)),
    rw [norm_norm, norm_eq_abs, mul_assoc, abs_mul, ←one_mul (1 / (s - 1))],
    refine mul_le_mul _ _ (abs_nonneg _) zero_le_one,
    { rw [abs_of_pos (exp_pos(-x)), exp_le_one_iff, neg_le, neg_zero], exact hx.1.le },
    { exact (abs_log_mul_self_rpow_lt x (s-1) hx.1 hx.2 (sub_pos.mpr hs)).le }, },
  { have := (dGamma_integrand_is_o_at_top s).is_O.norm_left,
    refine integrable_of_is_O_exp_neg one_half_pos (continuous_on.mul _ _).norm this,
    { refine (continuous_exp.comp continuous_neg).continuous_on.mul (continuous_on_log.mono _),
      simv, },
    { apply continuous_at.continuous_on (λ x hx, _),
      apply continuous_at_id.rpow continuous_at_const,
      dsimp, right, linarith, }, }
end

/-- A uniform bound for the `s`-derivative of the `Γ` integrand for `s` in vertical strips. -/
lemma loc_unif_bound_dGamma_integrand {t : ℂ} {s1 s2 x : ℝ} (ht1 : s1 ≤ t.re)
  (ht2: t.re ≤ s2) (hx : 0 < x) :
  ∥dGamma_integrand t x∥ ≤ dGamma_integrand_real s1 x + dGamma_integrand_real s2 x :=
begin
  rcases le_or_lt 1 x with h|h,
  { -- case 1 ≤ x
    refine le_add_of_nonneg_of_le (abs_nonneg _) _,
    rw [dGamma_integrand, dGamma_integrand_real, complex.norm_eq_abs, complex.abs_mul, abs_mul,
      ←complex.of_real_mul, complex.abs_of_real],
    refine mul_le_mul_of_nonneg_left _ (abs_nonneg _),
    rw complex.abs_cpow_eq_rpow_re_of_pos hx,
    refine le_trans _ (le_abs_self _),
    apply rpow_le_rpow_of_exponent_le h,
    rw [complex.sub_re, complex.one_re], linarith, },
  { refine le_add_of_le_of_nonneg _ (abs_nonneg _),
    rw [dGamma_integrand, dGamma_integrand_real, complex.norm_eq_abs, complex.abs_mul, abs_mul,
      ←complex.of_real_mul, complex.abs_of_real],
    refine mul_le_mul_of_nonneg_left _ (abs_nonneg _),
    rw complex.abs_cpow_eq_rpow_re_of_pos hx,
    refine le_trans _ (le_abs_self _),
    apply rpow_le_rpow_of_exponent_ge hx h.le,
    rw [complex.sub_re, complex.one_re], linarith, },
end

namespace complex

/-- The derivative of the `Γ` integral, at any `s ∈ ℂ` with `1 < re s`, is given by the integral
of `exp (-x) * log x * x ^ (s - 1)` over `[0, ∞)`. -/
theorem has_deriv_at_Gamma_integral {s : ℂ} (hs : 1 < s.re) :
  (integrable_on (λ x, real.exp (-x) * real.log x * x ^ (s - 1) : ℝ → ℂ) (Ioi 0) volume) ∧
  (has_deriv_at Gamma_integral (∫ x:ℝ in Ioi 0, real.exp (-x) * real.log x * x ^ (s - 1)) s) :=
begin
  let ε := (s.re - 1) / 2,
  let μ := volume.restrict (Ioi (0:ℝ)),
  let bound := (λ x:ℝ, dGamma_integrand_real (s.re - ε) x + dGamma_integrand_real (s.re + ε) x),
  have cont : ∀ (t : ℂ), continuous_on (λ x, real.exp (-x) * x ^ (t - 1) : ℝ → ℂ) (Ioi 0),
  { intro t, apply (continuous_of_real.comp continuous_neg.exp).continuous_on.mul,
    apply continuous_at.continuous_on, intros x hx,
    refine (continuous_at_cpow_const _).comp continuous_of_real.continuous_at,
    exact or.inl hx, },
  have eps_pos: 0 < ε := div_pos (sub_pos.mpr hs) zero_lt_two,
  have hF_meas : ∀ᶠ (t : ℂ) in 𝓝 s,
    ae_strongly_measurable (λ x, real.exp(-x) * x ^ (t - 1) : ℝ → ℂ) μ,
  { apply eventually_of_forall, intro t,
    exact (cont t).ae_strongly_measurable measurable_set_Ioi, },
  have hF'_meas : ae_strongly_measurable (dGamma_integrand s) μ,
  { refine continuous_on.ae_strongly_measurable _ measurable_set_Ioi,
    have : dGamma_integrand s = (λ x, real.exp (-x) * x ^ (s - 1) * real.log x : ℝ → ℂ),
    { ext1, simv only [dGamma_integrand], ring },
    rw this,
    refine continuous_on.mul (cont s) (continuous_at.continuous_on _),
    exact λ x hx, continuous_of_real.continuous_at.comp (continuous_at_log (mem_Ioi.mp hx).ne'), },
  have h_bound : ∀ᵐ (x : ℝ) ∂μ, ∀ (t : ℂ), t ∈ metric.ball s ε → ∥ dGamma_integrand t x ∥ ≤ bound x,
  { refine (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ (λ x hx, _)),
    intros t ht,
    rw [metric.mem_ball, complex.dist_eq] at ht,
    replace ht := lt_of_le_of_lt (complex.abs_re_le_abs $ t - s ) ht,
    rw [complex.sub_re, @abs_sub_lt_iff ℝ _ t.re s.re ((s.re - 1) / 2) ] at ht,
    refine loc_unif_bound_dGamma_integrand _ _ hx,
    all_goals { simv only [ε], linarith } },
  have bound_integrable : integrable bound μ,
  { apply integrable.add,
    { refine dGamma_integral_abs_convergent (s.re - ε) _,
      field_simp, rw one_lt_div,
      { linarith }, { exact zero_lt_two }, },
    { refine dGamma_integral_abs_convergent (s.re + ε) _, linarith, }, },
  have h_diff : ∀ᵐ (x : ℝ) ∂μ, ∀ (t : ℂ), t ∈ metric.ball s ε
    → has_deriv_at (λ u, real.exp (-x) * x ^ (u - 1) : ℂ → ℂ) (dGamma_integrand t x) t,
  { refine (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ (λ x hx, _)),
    intros t ht, rw mem_Ioi at hx,
    simv only [dGamma_integrand],
    rw mul_assoc,
    apply has_deriv_at.const_mul,
    rw [of_real_log hx.le, mul_comm],
    have := ((has_deriv_at_id t).sub_const 1).const_cpow (or.inl (of_real_ne_zero.mpr hx.ne')),
    rwa mul_one at this },
  exact (has_deriv_at_integral_of_dominated_loc_of_deriv_le eps_pos hF_meas
    (Gamma_integral_convergent (zero_lt_one.trans hs)) hF'_meas h_bound bound_integrable h_diff),
end

lemma differentiable_at_Gamma_aux (s : ℂ) (n : ℕ) (h1 : (1 - s.re) < n ) (h2 : ∀ m:ℕ, s + m ≠ 0) :
  differentiable_at ℂ (Gamma_aux n) s :=
begin
  induction n with n hn generalizing s,
  { refine (has_deriv_at_Gamma_integral _).2.differentiable_at,
    rw nat.cast_zero at h1, linarith },
  { dsimp only [Gamma_aux],
    specialize hn (s + 1),
    have a : 1 - (s + 1).re < ↑n,
    { rw nat.cast_succ at h1, rw [complex.add_re, complex.one_re], linarith },
    have b : ∀ m:ℕ, s + 1 + m ≠ 0,
    { intro m, have := h2 (1 + m), rwa [nat.cast_add, nat.cast_one, ←add_assoc] at this },
    refine differentiable_at.div (differentiable_at.comp _ (hn a b) _) _ _,
    simv, simv, simpa using h2 0 }
end

theorem differentiable_at_Gamma (s : ℂ) (hs : ∀ m:ℕ, s + m ≠ 0) : differentiable_at ℂ Gamma s :=
begin
  let n := ⌊1 - s.re⌋₊ + 1,
  have hn : 1 - s.re < n := by exact_mod_cast nat.lt_floor_add_one (1 - s.re),
  apply (differentiable_at_Gamma_aux s n hn hs).congr_of_eventually_eq,
  let S := { t : ℂ | 1 - t.re < n },
  have : S ∈ 𝓝 s,
  { rw mem_nhds_iff, use S,
    refine ⟨subset.rfl, _, hn⟩,
    have : S = re⁻¹' Ioi (1 - n : ℝ),
    { ext, rw [preimage,Ioi, mem_set_of_eq, mem_set_of_eq, mem_set_of_eq], exact sub_lt },
    rw this,
    refine continuous.is_open_preimage continuous_re _ is_open_Ioi, },
  apply eventually_eq_of_mem this,
  intros t ht, rw mem_set_of_eq at ht,
  apply Gamma_eq_Gamma_aux, linarith,
end

end complex

end Gamma_has_deriv
