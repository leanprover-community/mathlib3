/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import measure_theory.integral.exp_decay
import analysis.calculus.parametric_integral
import analysis.special_functions.integrals

/-!
# The Gamma function

This file defines the `Γ` function (of a real or complex variable `s`). We define this by Euler's
integral `Γ(s) = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1)` in the range where this integral converges
(i.e., for `0 < s` in the real case, and `0 < re s` in the complex case).

We show that this integral satisfies `Γ(1) = 1` and `Γ(s + 1) = s * Γ(s)`; hence we can define
`Γ(s)` for all `s` as the unique function satisfying this recurrence and agreeing with Euler's
integral in the convergence range. In the complex case we also prove that the resulting function is
holomorphic on `ℂ` away from the points `{-n : n ∈ ℕ}`.

## Main statements (real case)

* `real.Gamma` : the `Γ` function (of a real variable).
* `real.Gamma_eq_integral` : for `0 < s`, `Γ(s)` agrees with Euler's integral
  `∫ (x:ℝ) in Ioi 0, exp (-x) * x ^ (s - 1)`
* `real.Gamma_add_one` : for all `s : ℝ` with `s ≠ 0`, we have `Γ(s + 1) = s Γ(s)`.
* `real.Gamma_nat_eq_factorial` : for all `n : ℕ` we have `Γ (n + 1) = n!`.
* `real.differentiable_at_Gamma` : `Γ` is real-differentiable at all `s : ℝ` with
  `s ∉ {-n : n ∈ ℕ}`.
* `real.Gamma_ne_zero`: for all `s : ℝ` with `s ∉ {-n : n ∈ ℕ}` we have `Γ s ≠ 0`.
* `real.tendsto_log_Gamma`: for all `0 < s`, the limit as `n → ∞` of the sequence
  `n ↦ s log n + log n! - (log s + ... + log (s + n))` is `log Γ(s)`.
* `real.convex_on_log_Gamma` : `log ∘ Γ` is convex on `Ioi 0`.
* `real.eq_Gamma_of_log_convex` : the Bohr-Mollerup theorem, which states that the `Γ` function is
  the unique log-convex, positive-valued function on `Ioi 0` satisfying the functional equation
  and having `Γ 1 = 1`.

## Main statements (complex case)

* `complex.Gamma` : the `Γ` function (of a complex variable).
* `complex.Gamma_eq_integral` : for `0 < re s`, `Γ(s)` agrees with Euler's integral.
* `complex.Gamma_add_one` : for all `s : ℂ` with `s ≠ 0`, we have `Γ(s + 1) = s Γ(s)`.
* `complex.Gamma_nat_eq_factorial` : for all `n : ℕ` we have `Γ (n + 1) = n!`.
* `complex.differentiable_at_Gamma` : `Γ` is complex-differentiable at all `s : ℂ` with
  `s ∉ {-n : n ∈ ℕ}`.

## Tags

Gamma
-/

noncomputable theory
open filter interval_integral set real measure_theory asymptotics
open_locale nat topological_space ennreal big_operators

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

/-- The Euler integral for the `Γ` function converges for positive real `s`. -/
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
    rw [norm_eq_abs, map_mul, abs_of_nonneg $ le_of_lt $ exp_pos $ -x,
      abs_cpow_eq_rpow_re_of_pos hx _],
    simp }
end

/-- Euler's integral for the `Γ` function (of a complex variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `complex.Gamma_integral_convergent` for a proof of the convergence of the integral for
`0 < re s`. -/
def Gamma_integral (s : ℂ) : ℂ := ∫ x in Ioi (0:ℝ), ↑(-x).exp * ↑x ^ (s - 1)

lemma Gamma_integral_of_real (s : ℝ) :
  Gamma_integral ↑s = ↑(∫ x:ℝ in Ioi 0, real.exp (-x) * x ^ (s - 1)) :=
begin
  rw [Gamma_integral, ←_root_.integral_of_real],
  refine set_integral_congr measurable_set_Ioi _,
  intros x hx, dsimp only,
  rw [of_real_mul, of_real_cpow (mem_Ioi.mp hx).le],
  simp,
end

lemma Gamma_integral_one : Gamma_integral 1 = 1 :=
by simpa only [←of_real_one, Gamma_integral_of_real, of_real_inj, sub_self,
  rpow_zero, mul_one] using integral_exp_neg_Ioi

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
  { ext1, simp only [add_sub_cancel, pi.neg_apply] },
  { simp only [add_re, one_re], linarith,},
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
  simp_rw [norm_eq_abs, map_mul],
  refine (((real.Gamma_integral_convergent hs).mono_set
    Ioc_subset_Ioi_self).has_finite_integral.congr _).const_mul _,
  rw [eventually_eq, ae_restrict_iff'],
  { apply ae_of_all, intros x hx,
    rw [abs_of_nonneg (exp_pos _).le,abs_cpow_eq_rpow_re_of_pos hx.1],
    simp },
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
    have d2 : has_deriv_at (λ (y : ℝ), ↑y ^ s) (s * x ^ (s - 1)) x,
    { have t := @has_deriv_at.cpow_const _ _ _ s (has_deriv_at_id ↑x) _,
      simpa only [mul_one] using t.comp_of_real,
      simpa only [id.def, of_real_re, of_real_im,
        ne.def, eq_self_iff_true, not_true, or_false, mul_one] using hx.1, },
    simpa only [of_real_neg, neg_mul] using d1.of_real_comp.mul d2 },
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
  rw [eq_sub_of_add_eq int_eval, sub_neg_eq_add, neg_sub, add_comm, add_sub],
  simp only [sub_left_inj, add_left_inj],
  have : (λ x, (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) = (λ x, s * (-x).exp * x ^ (s - 1) : ℝ → ℂ),
  { ext1, ring,},
  rw this,
  have t := @integral_const_mul 0 X volume _ _ s (λ x:ℝ, (-x).exp * x ^ (s - 1)),
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
  have : (λ (e : ℝ), ‖-(e:ℂ) ^ s * (-e).exp‖ ) =ᶠ[at_top] (λ (e : ℝ), e ^ s.re * (-1 * e).exp ),
  { refine eventually_eq_of_mem (Ioi_mem_at_top 0) _,
    intros x hx, dsimp only,
    rw [norm_eq_abs, map_mul, abs.map_neg, abs_cpow_eq_rpow_re_of_pos hx,
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
  { simp only [nat.cast_zero, neg_lt_zero] at h1,
    dsimp only [Gamma_aux], rw Gamma_integral_add_one h1,
    rw [mul_comm, mul_div_cancel], contrapose! h1, rw h1,
    simp },
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
  { simp only [nat.cast_zero, neg_lt_zero] at h1,
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
@[pp_nodot] def Gamma (s : ℂ) : ℂ := Gamma_aux ⌊1 - s.re⌋₊ s

lemma Gamma_eq_Gamma_aux (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) : Gamma s = Gamma_aux n s :=
begin
  have u : ∀ (k : ℕ), Gamma_aux (⌊1 - s.re⌋₊ + k) s = Gamma s,
  { intro k, induction k with k hk,
    { simp [Gamma],},
    { rw [←hk, nat.succ_eq_add_one, ←add_assoc],
      refine (Gamma_aux_recurrence2 s (⌊1 - s.re⌋₊ + k) _).symm,
      rw nat.cast_add,
      have i0 := nat.sub_one_lt_floor (1 - s.re),
      simp only [sub_sub_cancel_left] at i0,
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

theorem Gamma_eq_integral {s : ℂ} (hs : 0 < s.re) : Gamma s = Gamma_integral s :=
Gamma_eq_Gamma_aux s 0 (by { norm_cast, linarith })

lemma Gamma_one : Gamma 1 = 1 :=
by { rw Gamma_eq_integral, simpa using Gamma_integral_one, simp }

theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n+1) = n! :=
begin
  induction n with n hn,
  { simpa using Gamma_one },
  { rw (Gamma_add_one n.succ $ nat.cast_ne_zero.mpr $ nat.succ_ne_zero n),
    simp only [nat.cast_succ, nat.factorial_succ, nat.cast_mul], congr, exact hn },
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
  intros x hx, simp [exp_log hx],
end

/-- Absolute convergence of the integral which will give the derivative of the `Γ` function on
`1 < re s`. -/
lemma dGamma_integral_abs_convergent (s : ℝ) (hs : 1 < s) :
  integrable_on (λ x:ℝ, ‖exp (-x) * log x * x ^ (s-1)‖) (Ioi 0) :=
begin
  rw [←Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrable_on_union],
  refine ⟨⟨_, _⟩, _⟩,
  { refine continuous_on.ae_strongly_measurable (continuous_on.mul _ _).norm measurable_set_Ioc,
    { refine (continuous_exp.comp continuous_neg).continuous_on.mul (continuous_on_log.mono _),
      simp, },
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
      simp, },
    { apply continuous_at.continuous_on (λ x hx, _),
      apply continuous_at_id.rpow continuous_at_const,
      dsimp, right, linarith, }, }
end

/-- A uniform bound for the `s`-derivative of the `Γ` integrand for `s` in vertical strips. -/
lemma loc_unif_bound_dGamma_integrand {t : ℂ} {s1 s2 x : ℝ} (ht1 : s1 ≤ t.re)
  (ht2: t.re ≤ s2) (hx : 0 < x) :
  ‖dGamma_integrand t x‖ ≤ dGamma_integrand_real s1 x + dGamma_integrand_real s2 x :=
begin
  rcases le_or_lt 1 x with h|h,
  { -- case 1 ≤ x
    refine le_add_of_nonneg_of_le (abs_nonneg _) _,
    rw [dGamma_integrand, dGamma_integrand_real, complex.norm_eq_abs, map_mul, abs_mul,
      ←complex.of_real_mul, complex.abs_of_real],
    refine mul_le_mul_of_nonneg_left _ (abs_nonneg _),
    rw complex.abs_cpow_eq_rpow_re_of_pos hx,
    refine le_trans _ (le_abs_self _),
    apply rpow_le_rpow_of_exponent_le h,
    rw [complex.sub_re, complex.one_re], linarith, },
  { refine le_add_of_le_of_nonneg _ (abs_nonneg _),
    rw [dGamma_integrand, dGamma_integrand_real, complex.norm_eq_abs, map_mul, abs_mul,
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
    { ext1, simp only [dGamma_integrand], ring },
    rw this,
    refine continuous_on.mul (cont s) (continuous_at.continuous_on _),
    exact λ x hx, continuous_of_real.continuous_at.comp (continuous_at_log (mem_Ioi.mp hx).ne'), },
  have h_bound : ∀ᵐ (x : ℝ) ∂μ, ∀ (t : ℂ), t ∈ metric.ball s ε → ‖ dGamma_integrand t x ‖ ≤ bound x,
  { refine (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ (λ x hx, _)),
    intros t ht,
    rw [metric.mem_ball, complex.dist_eq] at ht,
    replace ht := lt_of_le_of_lt (complex.abs_re_le_abs $ t - s ) ht,
    rw [complex.sub_re, @abs_sub_lt_iff ℝ _ t.re s.re ((s.re - 1) / 2) ] at ht,
    refine loc_unif_bound_dGamma_integrand _ _ hx,
    all_goals { simp only [ε], linarith } },
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
    simp only [dGamma_integrand],
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
    simp, simp, simpa using h2 0 }
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
    { ext, rw [preimage,Ioi, mem_set_of_eq, mem_set_of_eq, mem_set_of_eq], exact sub_lt_comm },
    rw this,
    refine continuous.is_open_preimage continuous_re _ is_open_Ioi, },
  apply eventually_eq_of_mem this,
  intros t ht, rw mem_set_of_eq at ht,
  apply Gamma_eq_Gamma_aux, linarith,
end

end complex

end Gamma_has_deriv

namespace real

/-- The `Γ` function (of a real variable `s`). -/
@[pp_nodot] def Gamma (s : ℝ) : ℝ := (complex.Gamma s).re

lemma Gamma_eq_integral {s : ℝ} (hs : 0 < s) : Gamma s = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1) :=
begin
  rw [Gamma, complex.Gamma_eq_integral (by rwa complex.of_real_re : 0 < complex.re s)],
  dsimp only [complex.Gamma_integral],
  simp_rw [←complex.of_real_one, ←complex.of_real_sub],
  suffices : ∫ (x : ℝ) in Ioi 0, ↑(exp (-x)) * (x : ℂ) ^ ((s - 1 : ℝ) : ℂ) =
    ∫ (x : ℝ) in Ioi 0, ((exp (-x) * x ^ (s - 1) : ℝ) : ℂ),
  { rw [this, _root_.integral_of_real, complex.of_real_re], },
  refine set_integral_congr measurable_set_Ioi (λ x hx, _),
  push_cast,
  rw complex.of_real_cpow (le_of_lt hx),
  push_cast,
end

lemma Gamma_add_one {s : ℝ} (hs : s ≠ 0) : Gamma (s + 1) = s * Gamma s :=
begin
  simp_rw Gamma,
  rw [complex.of_real_add, complex.of_real_one, complex.Gamma_add_one, complex.of_real_mul_re],
  rwa complex.of_real_ne_zero,
end

lemma Gamma_one : Gamma 1 = 1 :=
by rw [Gamma, complex.of_real_one, complex.Gamma_one, complex.one_re]

theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n + 1) = n! :=
by rw [Gamma, complex.of_real_add, complex.of_real_nat_cast, complex.of_real_one,
  complex.Gamma_nat_eq_factorial, ←complex.of_real_nat_cast, complex.of_real_re]

lemma Gamma_pos_of_pos {s : ℝ} (hs : 0 < s) : 0 < Gamma s :=
begin
  rw Gamma_eq_integral hs,
  have : function.support (λ (x : ℝ), exp (-x) * x ^ (s - 1)) ∩ Ioi 0 = Ioi 0,
  { rw inter_eq_right_iff_subset,
    intros x hx,
    rw function.mem_support,
    exact mul_ne_zero (exp_pos _).ne' (rpow_pos_of_pos hx _).ne' },
  rw set_integral_pos_iff_support_of_nonneg_ae,
  { rw [this, volume_Ioi, ←ennreal.of_real_zero],
    exact ennreal.of_real_lt_top },
  { refine eventually_of_mem (self_mem_ae_restrict measurable_set_Ioi) _,
    exact λ x hx, (mul_pos (exp_pos _) (rpow_pos_of_pos hx _)).le },
  { exact Gamma_integral_convergent hs },
end

lemma Gamma_ne_zero {s : ℝ} (hs : ∀ m:ℕ, s + m ≠ 0) : Gamma s ≠ 0 :=
begin
  suffices : ∀ {n : ℕ}, (-(n:ℝ) < s) → Gamma s ≠ 0,
  { apply this,
    swap, use (⌊-s⌋₊ + 1),
    rw [neg_lt, nat.cast_add, nat.cast_one],
    exact nat.lt_floor_add_one _ },
  intro n,
  induction n generalizing s,
  { intro hs,
    refine (Gamma_pos_of_pos _).ne',
    rwa [nat.cast_zero, neg_zero] at hs },
  { intro hs',
    have : Gamma (s + 1) ≠ 0,
    { apply n_ih,
      { intro m,
        convert hs (1 + m) using 1,
        push_cast,
        ring,  },
      { rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one, neg_add] at hs',
        linarith }  },
    rw [Gamma_add_one, mul_ne_zero_iff] at this,
    { exact this.2 },
    { simpa using hs 0 } },
end

lemma differentiable_at_Gamma {s : ℝ} (hs : ∀ m:ℕ, s + m ≠ 0) : differentiable_at ℝ Gamma s :=
begin
  apply has_deriv_at.differentiable_at,
  apply has_deriv_at.real_of_complex,
  apply differentiable_at.has_deriv_at,
  apply complex.differentiable_at_Gamma,
  simp_rw [←complex.of_real_nat_cast, ←complex.of_real_add, complex.of_real_ne_zero],
  exact hs,
end

/-- Log-convexity of the Gamma function on the positive reals (stated in multiplicative form),
proved using the Hölder inequality applied to Euler's integral. -/
lemma Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma {s t a b : ℝ}
  (hs : 0 < s) (ht : 0 < t) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
  Gamma (a * s + b * t) ≤ Gamma s ^ a * Gamma t ^ b :=
begin
  -- We will apply Hölder's inequality, for the conjugate exponents `p = 1 / a`
  -- and `q = 1 / b`, to the functions `f a s` and `f b t`, where `f` is as follows:
  let f : ℝ → ℝ → ℝ → ℝ := λ c u x, exp (-c * x) * x ^ (c * (u - 1)),
  have e : is_conjugate_exponent (1 / a) (1 / b) := real.is_conjugate_exponent_one_div ha hb hab,
  have hab' : b = 1 - a := by linarith,
  have hst : 0 < a * s + b * t := add_pos (mul_pos ha hs) (mul_pos hb ht),
  -- some properties of f:
  have posf : ∀ (c u x : ℝ), x ∈ Ioi (0:ℝ) → 0 ≤ f c u x :=
    λ c u x hx, mul_nonneg (exp_pos _).le (rpow_pos_of_pos hx _).le,
  have posf' : ∀ (c u : ℝ), ∀ᵐ (x : ℝ) ∂volume.restrict (Ioi 0), 0 ≤ f c u x :=
    λ c u, (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ (posf c u)),
  have fpow : ∀ {c x : ℝ} (hc : 0 < c) (u : ℝ) (hx : 0 < x),
    exp (-x) * x ^ (u - 1) = f c u x ^ (1 / c),
  { intros c x hc u hx,
    dsimp only [f],
    rw [mul_rpow (exp_pos _).le ((rpow_nonneg_of_nonneg hx.le) _), ←exp_mul, ←rpow_mul hx.le],
    congr' 2;
    { field_simp [hc.ne'], ring } },
  -- show `f c u` is in `ℒp` for `p = 1/c`:
  have f_mem_Lp : ∀ {c u : ℝ} (hc : 0 < c) (hu : 0 < u),
    mem_ℒp (f c u) (ennreal.of_real (1 / c)) (volume.restrict (Ioi 0)),
  { intros c u hc hu,
    have A : ennreal.of_real (1 / c) ≠ 0,
      by rwa [ne.def, ennreal.of_real_eq_zero, not_le, one_div_pos],
    have B : ennreal.of_real (1 / c) ≠ ∞, from ennreal.of_real_ne_top,
    rw [←mem_ℒp_norm_rpow_iff _ A B, ennreal.to_real_of_real (one_div_nonneg.mpr hc.le),
      ennreal.div_self A B, mem_ℒp_one_iff_integrable],
    { apply integrable.congr (Gamma_integral_convergent hu),
      refine eventually_eq_of_mem (self_mem_ae_restrict measurable_set_Ioi) (λ x hx, _),
      dsimp only,
      rw fpow hc u hx,
      congr' 1,
      exact (norm_of_nonneg (posf _ _ x hx)).symm },
    { refine continuous_on.ae_strongly_measurable _ measurable_set_Ioi,
      refine (continuous.continuous_on _).mul (continuous_at.continuous_on (λ x hx, _)),
      { exact continuous_exp.comp (continuous_const.mul continuous_id'), },
      { exact continuous_at_rpow_const _ _ (or.inl (ne_of_lt hx).symm), } } },
  -- now apply Hölder:
  rw [Gamma_eq_integral hs, Gamma_eq_integral ht, Gamma_eq_integral hst],
  convert measure_theory.integral_mul_le_Lp_mul_Lq_of_nonneg e (posf' a s) (posf' b t)
    (f_mem_Lp ha hs) (f_mem_Lp hb ht) using 1,
  { refine set_integral_congr measurable_set_Ioi (λ x hx, _),
    dsimp only [f],
    have A : exp (-x) = exp (-a * x) * exp (-b * x),
    { rw [←exp_add, ←add_mul, ←neg_add, hab, neg_one_mul] },
    have B : x ^ (a * s + b * t - 1) = (x ^ (a * (s - 1))) * (x ^ (b * (t - 1))),
    { rw [←rpow_add hx, hab'], congr' 1, ring },
    rw [A, B],
    ring },
  { rw [one_div_one_div, one_div_one_div],
    congr' 2;
    exact set_integral_congr measurable_set_Ioi (λ x hx, fpow (by assumption) _ hx) },
end

lemma convex_on_log_Gamma : convex_on ℝ (Ioi 0) (log ∘ Gamma) :=
begin
  refine convex_on_iff_forall_pos.mpr ⟨convex_Ioi _, λ x hx y hy a b ha hb hab, _⟩,
  have : b = 1 - a := by linarith, subst this,
  simp_rw [function.comp_app, smul_eq_mul],
  rw [←log_rpow (Gamma_pos_of_pos hy), ←log_rpow (Gamma_pos_of_pos hx),
    ←log_mul
      ((rpow_pos_of_pos (Gamma_pos_of_pos hx) _).ne') (rpow_pos_of_pos (Gamma_pos_of_pos hy) _).ne',
    log_le_log
      (Gamma_pos_of_pos (add_pos (mul_pos ha hx) (mul_pos hb hy)))
      (mul_pos
        (rpow_pos_of_pos (Gamma_pos_of_pos hx) _) (rpow_pos_of_pos (Gamma_pos_of_pos hy) _))],
  exact Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx hy ha hb hab,
end

section bohr_mollerup

/-! ## The Euler limit formula and the Bohr-Mollerup theorem

In this section we prove two interrelated statements about the `Γ` function on the positive reals:

* the Euler limit formula `real.tendsto_log_gamma_seq`, stating that the sequence
  `x * log n + log n! - ∑ (m : ℕ) in finset.range (n + 1), log (x + m)`
  tends to `log Γ(x)` as `n → ∞`.
* the Bohr-Mollerup theorem (`real.eq_Gamma_of_log_convex`) which states that `Γ` is the unique
  *log-convex*, positive-real-valued function on the positive reals satisfying
  `f (x + 1) = x f x` and `f 1 = 1`.

To do this, we prove that any function satisfying the hypotheses of the Bohr--Mollerup theorem must
agree with the limit in the Gauss formula, so there is at most one such function. Then we show that
`Γ` satisfies these conditions.
-/

/-- The function `n ↦ x log n + log n! - (log x + ... + log (x + n))`, which we will show tends to
`log (Gamma x)` as `n → ∞`. -/
def log_gamma_seq (x : ℝ) (n : ℕ) : ℝ :=
x * log n + log n! - ∑ (m : ℕ) in finset.range (n + 1), log (x + m)

/-! The following are auxiliary lemmas for the Bohr-Mollerup theorem, which are
placed in a separate namespace `bohr_mollerup` to avoid clutter. -/
namespace bohr_mollerup

variables {f : ℝ → ℝ} {x : ℝ} {n : ℕ}

lemma f_nat_eq (hf_feq : ∀ {y:ℝ}, 0 < y → f (y + 1) = f y + log y) (hn : n ≠ 0) :
  f n = f 1 + log (n - 1)! :=
begin
  refine nat.le_induction (by simp) (λ m hm IH, _) n (nat.one_le_iff_ne_zero.2 hn),
  have A : 0 < (m : ℝ), from nat.cast_pos.2 hm,
  simp only [hf_feq A, nat.cast_add, algebra_map.coe_one, nat.add_succ_sub_one, add_zero],
  rw [IH, add_assoc, ← log_mul (nat.cast_ne_zero.mpr (nat.factorial_ne_zero _)) A.ne',
    ← nat.cast_mul],
  conv_rhs { rw [← nat.succ_pred_eq_of_pos hm, nat.factorial_succ, mul_comm] },
  congr,
  exact (nat.succ_pred_eq_of_pos hm).symm
end

lemma f_add_nat_eq (hf_feq : ∀ {y:ℝ}, 0 < y → f (y + 1) = f y + log y) (hx : 0 < x) (n : ℕ) :
  f (x + n) = f x + ∑ (m : ℕ) in finset.range n, log (x + m) :=
begin
  induction n with n hn,
  { simp },
  { have : x + n.succ = (x + n) + 1,
    { push_cast, ring },
    rw [this, hf_feq, hn],
    rw [finset.range_succ, finset.sum_insert (finset.not_mem_range_self)],
    abel,
    linarith [(nat.cast_nonneg n : 0 ≤ (n:ℝ))] },
end

/-- Linear upper bound for `f (x + n)` on unit interval -/
lemma f_add_nat_le
  (hf_conv : convex_on ℝ (Ioi 0) f) (hf_feq : ∀ {y:ℝ}, 0 < y → f (y + 1) = f y + log y)
  (hn : n ≠ 0) (hx : 0 < x) (hx' : x ≤ 1) :
  f (n + x) ≤ f n + x * log n :=
begin
  have hn': 0 < (n:ℝ) := nat.cast_pos.mpr (nat.pos_of_ne_zero hn),
  have : f n + x * log n = (1 - x) * f n + x * f (n + 1),
  { rw [hf_feq hn'], ring, },
  rw [this, (by ring : (n:ℝ) + x = (1 - x) * n + x * (n + 1))],
  simpa only [smul_eq_mul] using hf_conv.2 hn' (by linarith : 0 < (n + 1 : ℝ))
    (by linarith : 0 ≤ 1 - x) hx.le (by linarith),
end

/-- Linear lower bound for `f (x + n)` on unit interval -/
lemma f_add_nat_ge
  (hf_conv : convex_on ℝ (Ioi 0) f) (hf_feq : ∀ {y:ℝ}, 0 < y → f (y + 1) = f y + log y)
  (hn : 2 ≤ n) (hx : 0 < x) :
  f n + x * log (n - 1) ≤ f (n + x) :=
begin
  have npos : 0 < (n:ℝ) - 1,
  { rw [←nat.cast_one, sub_pos, nat.cast_lt], linarith, },
  have c := (convex_on_iff_slope_mono_adjacent.mp $ hf_conv).2
    npos (by linarith : 0 < (n:ℝ) + x) (by linarith : (n:ℝ) - 1 < (n:ℝ)) (by linarith),
  rw [add_sub_cancel', sub_sub_cancel, div_one] at c,
  have : f (↑n - 1) = f n - log (↑n - 1),
  { nth_rewrite_rhs 0 (by ring : (n:ℝ) = (↑n - 1) + 1),
    rw [hf_feq npos, add_sub_cancel] },
  rwa [this, le_div_iff hx, sub_sub_cancel, le_sub_iff_add_le, mul_comm _ x, add_comm] at c,
end

lemma log_gamma_seq_add_one (x : ℝ) (n : ℕ) :
  log_gamma_seq (x + 1) n = log_gamma_seq x (n + 1) + log x - (x + 1) * (log (n + 1) - log n) :=
begin
  dsimp only [nat.factorial_succ, log_gamma_seq],
  conv_rhs { rw [finset.sum_range_succ', nat.cast_zero, add_zero],  },
  rw [nat.cast_mul, log_mul], rotate,
  { rw nat.cast_ne_zero, exact nat.succ_ne_zero n },
  { rw nat.cast_ne_zero, exact nat.factorial_ne_zero n, },
  have : ∑ (m : ℕ) in finset.range (n + 1), log (x + 1 + ↑m) =
    ∑ (k : ℕ) in finset.range (n + 1), log (x + ↑(k + 1)),
  { refine finset.sum_congr (by refl) (λ m hm, _),
    congr' 1,
    push_cast,
    abel },
  rw [←this, nat.cast_add_one n],
  ring,
end

lemma le_log_gamma_seq
  (hf_conv : convex_on ℝ (Ioi 0) f) (hf_feq : ∀ {y:ℝ}, 0 < y → f (y + 1) = f y + log y)
  (hx : 0 < x) (hx' : x ≤ 1) (n : ℕ) :
  f x ≤ f 1 + x * log (n + 1) - x * log n + log_gamma_seq x n :=
begin
  rw [log_gamma_seq, ←add_sub_assoc, le_sub_iff_add_le, ←f_add_nat_eq @hf_feq hx, add_comm x],
  refine (f_add_nat_le hf_conv @hf_feq (nat.add_one_ne_zero n) hx hx').trans (le_of_eq _),
  rw [f_nat_eq @hf_feq (by linarith : n + 1 ≠ 0), nat.add_sub_cancel, nat.cast_add_one],
  ring,
end

lemma ge_log_gamma_seq
  (hf_conv : convex_on ℝ (Ioi 0) f) (hf_feq : ∀ {y:ℝ}, 0 < y → f (y + 1) = f y + log y)
  (hx : 0 < x) (hn : n ≠ 0) :
  f 1 + log_gamma_seq x n ≤ f x :=
begin
  dsimp [log_gamma_seq],
  rw [←add_sub_assoc, sub_le_iff_le_add, ←f_add_nat_eq @hf_feq hx, add_comm x _],
  refine le_trans (le_of_eq _) (f_add_nat_ge hf_conv @hf_feq _ hx),
  { rw [f_nat_eq @hf_feq, nat.add_sub_cancel, nat.cast_add_one, add_sub_cancel],
    { ring },
    { exact nat.succ_ne_zero _} },
  { apply nat.succ_le_succ,
    linarith [nat.pos_of_ne_zero hn] },
end

lemma tendsto_log_gamma_seq_of_le_one
  (hf_conv : convex_on ℝ (Ioi 0) f) (hf_feq : ∀ {y:ℝ}, 0 < y → f (y + 1) = f y + log y)
  (hx : 0 < x) (hx' : x ≤ 1) :
  tendsto (log_gamma_seq x) at_top (𝓝 $ f x - f 1) :=
begin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' _ tendsto_const_nhds _ _,
  show ∀ᶠ (n : ℕ) in at_top, log_gamma_seq x n ≤ f x - f 1,
  { refine eventually.mp (eventually_ne_at_top 0) (eventually_of_forall (λ n hn, _)),
    exact le_sub_iff_add_le'.mpr (ge_log_gamma_seq hf_conv @hf_feq hx hn) },
  show ∀ᶠ (n : ℕ) in at_top, f x - f 1 - x * (log (n + 1) - log n) ≤ log_gamma_seq x n,
  { refine eventually_of_forall (λ n, _),
    rw [sub_le_iff_le_add', sub_le_iff_le_add'],
    convert le_log_gamma_seq hf_conv @hf_feq hx hx' n using 1,
    ring },
  { have : f x - f 1 = (f x - f 1) - x * 0 := by ring,
    nth_rewrite 0 this,
    exact tendsto.sub tendsto_const_nhds (tendsto_log_nat_add_one_sub_log.const_mul _), }
end

lemma tendsto_log_gamma_seq
  (hf_conv : convex_on ℝ (Ioi 0) f) (hf_feq : ∀ {y:ℝ}, 0 < y → f (y + 1) = f y + log y)
  (hx : 0 < x) :
  tendsto (log_gamma_seq x) at_top (𝓝 $ f x - f 1) :=
begin
  suffices : ∀ (m : ℕ), ↑m < x → x ≤ m + 1 →
    tendsto (log_gamma_seq x) at_top (𝓝 $ f x - f 1),
  { refine this (⌈x - 1⌉₊) _ _,
    { rcases lt_or_le x 1,
      { rwa [nat.ceil_eq_zero.mpr (by linarith : x - 1 ≤ 0), nat.cast_zero] },
      { convert nat.ceil_lt_add_one (by linarith : 0 ≤ x - 1),
        abel } },
    { rw ←sub_le_iff_le_add, exact nat.le_ceil _}, },
  intro m,
  induction m with m hm generalizing x,
  { rw [nat.cast_zero, zero_add],
    exact λ _ hx', tendsto_log_gamma_seq_of_le_one hf_conv @hf_feq hx hx' },
  { intros hy hy',
    rw [nat.cast_succ, ←sub_le_iff_le_add] at hy',
    rw [nat.cast_succ, ←lt_sub_iff_add_lt] at hy,
    specialize hm ((nat.cast_nonneg _).trans_lt hy) hy hy',
    -- now massage gauss_product n (x - 1) into gauss_product (n - 1) x
    have : ∀ᶠ (n:ℕ) in at_top, log_gamma_seq (x - 1) n = log_gamma_seq x (n - 1) +
      x * (log (↑(n - 1) + 1) - log ↑(n - 1)) - log (x - 1),
    { refine eventually.mp (eventually_ge_at_top 1) (eventually_of_forall (λ n hn, _)),
      have := log_gamma_seq_add_one (x - 1) (n - 1),
      rw [sub_add_cancel, nat.sub_add_cancel hn] at this,
      rw this,
      ring },
    replace hm := ((tendsto.congr' this hm).add
      (tendsto_const_nhds : tendsto (λ _, log (x - 1)) _ _)).comp (tendsto_add_at_top_nat 1),
    have :
      (λ (x_1 : ℕ), (λ (n : ℕ), log_gamma_seq x (n - 1) +
      x * (log (↑(n - 1) + 1) - log ↑(n - 1)) - log (x - 1)) x_1 +
      (λ (b : ℕ), log (x - 1)) x_1) ∘ (λ (a : ℕ), a + 1) =
      λ n, log_gamma_seq x n + x * (log (↑n + 1) - log ↑n),
    { ext1 n,
      dsimp only [function.comp_app],
      rw [sub_add_cancel, nat.add_sub_cancel] },
    rw this at hm,
    convert hm.sub (tendsto_log_nat_add_one_sub_log.const_mul x) using 2,
    { ext1 n, ring },
    { have := hf_feq ((nat.cast_nonneg m).trans_lt hy),
      rw sub_add_cancel at this,
      rw this,
      ring } },
end

end bohr_mollerup

lemma tendsto_log_Gamma {x : ℝ} (hx : 0 < x) :
  tendsto (log_gamma_seq x) at_top (𝓝 $ log (Gamma x)) :=
begin
  have : log (Gamma x) = (log ∘ Gamma) x - (log ∘ Gamma) 1,
  { simp_rw [function.comp_app, Gamma_one, log_one, sub_zero] },
  rw this,
  refine bohr_mollerup.tendsto_log_gamma_seq convex_on_log_Gamma (λ y hy, _) hx,
  rw [function.comp_app, Gamma_add_one hy.ne', log_mul hy.ne' (Gamma_pos_of_pos hy).ne', add_comm],
end

/-- The **Bohr-Mollerup theorem**: the Gamma function is the *unique* log-convex, positive-valued
function on the positive reals which satisfies `f 1 = 1` and `f (x + 1) = x * f x` for all `x`. -/
lemma eq_Gamma_of_log_convex {f : ℝ → ℝ}
  (hf_conv : convex_on ℝ (Ioi 0) (log ∘ f))
  (hf_feq : ∀ {y:ℝ}, 0 < y → f (y + 1) = y * f y)
  (hf_pos : ∀ {y:ℝ}, 0 < y → 0 < f y)
  (hf_one : f 1 = 1) :
  eq_on f Gamma (Ioi (0:ℝ)) :=
begin
  suffices : eq_on (log ∘ f) (log ∘ Gamma) (Ioi (0:ℝ)),
    from λ x hx, log_inj_on_pos (hf_pos hx) (Gamma_pos_of_pos hx) (this hx),
  intros x hx,
  have e1 := bohr_mollerup.tendsto_log_gamma_seq hf_conv _ hx,
  { rw [function.comp_app log f 1, hf_one, log_one, sub_zero] at e1,
    exact tendsto_nhds_unique e1 (tendsto_log_Gamma hx) },
  { intros y hy,
    rw [function.comp_app, hf_feq hy, log_mul hy.ne' (hf_pos hy).ne'],
    ring }
end

end bohr_mollerup

end real
