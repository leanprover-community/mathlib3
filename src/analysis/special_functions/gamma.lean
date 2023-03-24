/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import measure_theory.integral.exp_decay
import analysis.calculus.parametric_integral
import analysis.special_functions.integrals
import analysis.convolution
import analysis.special_functions.trigonometric.euler_sine_prod

/-!
# The Gamma and Beta functions

This file defines the `Γ` function (of a real or complex variable `s`). We define this by Euler's
integral `Γ(s) = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1)` in the range where this integral converges
(i.e., for `0 < s` in the real case, and `0 < re s` in the complex case).

We show that this integral satisfies `Γ(1) = 1` and `Γ(s + 1) = s * Γ(s)`; hence we can define
`Γ(s)` for all `s` as the unique function satisfying this recurrence and agreeing with Euler's
integral in the convergence range. (If `s = -n` for `n ∈ ℕ`, then the function is undefined, and we
set it to be `0` by convention.)

## Gamma function: main statements (complex case)

* `complex.Gamma`: the `Γ` function (of a complex variable).
* `complex.Gamma_eq_integral`: for `0 < re s`, `Γ(s)` agrees with Euler's integral.
* `complex.Gamma_add_one`: for all `s : ℂ` with `s ≠ 0`, we have `Γ (s + 1) = s Γ(s)`.
* `complex.Gamma_nat_eq_factorial`: for all `n : ℕ` we have `Γ (n + 1) = n!`.
* `complex.differentiable_at_Gamma`: `Γ` is complex-differentiable at all `s : ℂ` with
  `s ∉ {-n : n ∈ ℕ}`.
* `complex.Gamma_ne_zero`: for all `s : ℂ` with `s ∉ {-n : n ∈ ℕ}` we have `Γ s ≠ 0`.
* `complex.Gamma_seq_tendsto_Gamma`: for all `s`, the limit as `n → ∞` of the sequence
  `n ↦ n ^ s * n! / (s * (s + 1) * ... * (s + n))` is `Γ(s)`.
* `complex.Gamma_mul_Gamma_one_sub`: Euler's reflection formula
  `Gamma s * Gamma (1 - s) = π / sin π s`.

## Gamma function: main statements (real case)

* `real.Gamma`: the `Γ` function (of a real variable).
* Real counterparts of all the properties of the complex Gamma function listed above:
  `real.Gamma_eq_integral`, `real.Gamma_add_one`, `real.Gamma_nat_eq_factorial`,
  `real.differentiable_at_Gamma`, `real.Gamma_ne_zero`, `real.Gamma_seq_tendsto_Gamma`,
  `real.Gamma_mul_Gamma_one_sub`.
* `real.convex_on_log_Gamma` : `log ∘ Γ` is convex on `Ioi 0`.
* `real.eq_Gamma_of_log_convex` : the Bohr-Mollerup theorem, which states that the `Γ` function is
  the unique log-convex, positive-valued function on `Ioi 0` satisfying the functional equation
  and having `Γ 1 = 1`.

## Beta function

* `complex.beta_integral`: the Beta function `Β(u, v)`, where `u`, `v` are complex with positive
  real part.
* `complex.Gamma_mul_Gamma_eq_beta_integral`: the formula
  `Gamma u * Gamma v = Gamma (u + v) * beta_integral u v`.

## Tags

Gamma
-/

noncomputable theory
open filter interval_integral set real measure_theory asymptotics
open_locale nat topology ennreal big_operators complex_conjugate

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

lemma Gamma_integral_conj (s : ℂ) : Gamma_integral (conj s) = conj (Gamma_integral s) :=
begin
  rw [Gamma_integral, Gamma_integral, ←integral_conj],
  refine set_integral_congr measurable_set_Ioi (λ x hx, _),
  dsimp only,
  rw [ring_hom.map_mul, conj_of_real, cpow_def_of_ne_zero (of_real_ne_zero.mpr (ne_of_gt hx)),
    cpow_def_of_ne_zero (of_real_ne_zero.mpr (ne_of_gt hx)), ←exp_conj, ring_hom.map_mul,
    ←of_real_log (le_of_lt hx), conj_of_real, ring_hom.map_sub, ring_hom.map_one],
end

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

/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
lemma Gamma_zero : Gamma 0 = 0 :=
by simp_rw [Gamma, zero_re, sub_zero, nat.floor_one, Gamma_aux, div_zero]

/-- At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it the value 0. -/
lemma Gamma_neg_nat_eq_zero (n : ℕ) : Gamma (-n) = 0 :=
begin
  induction n with n IH,
  { rw [nat.cast_zero, neg_zero, Gamma_zero] },
  { have A : -(n.succ : ℂ) ≠ 0,
    { rw [neg_ne_zero, nat.cast_ne_zero],
      apply nat.succ_ne_zero },
    have : -(n:ℂ) = -↑n.succ + 1, by simp,
    rw [this, Gamma_add_one _ A] at IH,
    contrapose! IH,
    exact mul_ne_zero A IH }
end

lemma Gamma_conj (s : ℂ) : Gamma (conj s) = conj (Gamma s) :=
begin
  suffices : ∀ (n:ℕ) (s:ℂ) , Gamma_aux n (conj s) = conj (Gamma_aux n s), from this _ _,
  intro n,
  induction n with n IH,
  { rw Gamma_aux, exact Gamma_integral_conj, },
  { intro s,
    rw Gamma_aux,
    dsimp only,
    rw [div_eq_mul_inv _ s, ring_hom.map_mul, conj_inv, ←div_eq_mul_inv],
    suffices : conj s + 1 = conj (s + 1), by rw [this, IH],
    rw [ring_hom.map_add, ring_hom.map_one] }
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

lemma differentiable_at_Gamma_aux (s : ℂ) (n : ℕ) (h1 : (1 - s.re) < n ) (h2 : ∀ m : ℕ, s ≠ -m) :
  differentiable_at ℂ (Gamma_aux n) s :=
begin
  induction n with n hn generalizing s,
  { refine (has_deriv_at_Gamma_integral _).2.differentiable_at,
    rw nat.cast_zero at h1, linarith },
  { dsimp only [Gamma_aux],
    specialize hn (s + 1),
    have a : 1 - (s + 1).re < ↑n,
    { rw nat.cast_succ at h1, rw [complex.add_re, complex.one_re], linarith },
    have b : ∀ m : ℕ, s + 1 ≠ -m,
    { intro m, have := h2 (1 + m),
      contrapose! this,
      rw ←eq_sub_iff_add_eq at this,
      simpa using this },
    refine differentiable_at.div (differentiable_at.comp _ (hn a b) _) _ _,
    simp, simp, simpa using h2 0 }
end

theorem differentiable_at_Gamma (s : ℂ) (hs : ∀ m : ℕ, s ≠ -m) : differentiable_at ℂ Gamma s :=
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

lemma _root_.complex.Gamma_of_real (s : ℝ) : complex.Gamma (s : ℂ) = Gamma s :=
by rw [Gamma, eq_comm, ←complex.eq_conj_iff_re, ←complex.Gamma_conj, complex.conj_of_real]

theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n + 1) = n! :=
by rw [Gamma, complex.of_real_add, complex.of_real_nat_cast, complex.of_real_one,
  complex.Gamma_nat_eq_factorial, ←complex.of_real_nat_cast, complex.of_real_re]

/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
lemma Gamma_zero : Gamma 0 = 0 :=
by simpa only [←complex.of_real_zero, complex.Gamma_of_real, complex.of_real_inj]
  using complex.Gamma_zero

/-- At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it the value `0`.
-/
lemma Gamma_neg_nat_eq_zero (n : ℕ) : Gamma (-n) = 0 :=
begin
  simpa only [←complex.of_real_nat_cast, ←complex.of_real_neg, complex.Gamma_of_real,
    complex.of_real_eq_zero] using complex.Gamma_neg_nat_eq_zero n,
end

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

/-- The Gamma function does not vanish on `ℝ` (except at non-positive integers, where the function
is mathematically undefined and we set it to `0` by convention). -/
lemma Gamma_ne_zero {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : Gamma s ≠ 0 :=
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
        specialize hs (1 + m),
        contrapose! hs,
        rw ←eq_sub_iff_add_eq at hs,
        rw hs,
        push_cast,
        ring },
      { rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one, neg_add] at hs',
        linarith }  },
    rw [Gamma_add_one, mul_ne_zero_iff] at this,
    { exact this.2 },
    { simpa using hs 0 } },
end

lemma Gamma_eq_zero_iff (s : ℝ) : Gamma s = 0 ↔ ∃ m : ℕ, s = -m :=
⟨by { contrapose!, exact Gamma_ne_zero }, by { rintro ⟨m, rfl⟩, exact Gamma_neg_nat_eq_zero m }⟩

lemma differentiable_at_Gamma {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : differentiable_at ℝ Gamma s :=
begin
  refine ((complex.differentiable_at_Gamma _ _).has_deriv_at).real_of_complex.differentiable_at,
  simp_rw [←complex.of_real_nat_cast, ←complex.of_real_neg, ne.def, complex.of_real_inj],
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

lemma convex_on_Gamma : convex_on ℝ (Ioi 0) Gamma :=
begin
  refine ⟨convex_Ioi 0, λ x hx y hy a b ha hb hab, _⟩,
  have := convex_on.comp (convex_on_exp.subset (subset_univ _) _) convex_on_log_Gamma
    (λ u hu v hv huv, exp_le_exp.mpr huv),
  convert this.2 hx hy ha hb hab,
  { rw [function.comp_app, exp_log (Gamma_pos_of_pos $ this.1 hx hy ha hb hab)] },
  { rw [function.comp_app, exp_log (Gamma_pos_of_pos hx)] },
  { rw [function.comp_app, exp_log (Gamma_pos_of_pos hy)] },
  { rw convex_iff_is_preconnected,
    refine is_preconnected_Ioi.image _ (λ x hx, continuous_at.continuous_within_at _),
    refine (differentiable_at_Gamma (λ m, _)).continuous_at.log (Gamma_pos_of_pos hx).ne',
    exact (neg_lt_iff_pos_add.mpr (add_pos_of_pos_of_nonneg hx (nat.cast_nonneg m))).ne' }
end

section bohr_mollerup

/-! ## The Bohr-Mollerup theorem

In this section we prove two interrelated statements about the `Γ` function on the positive reals:

* the Euler limit formula `real.bohr_mollerup.tendsto_log_gamma_seq`, stating that for positive
  real `x` the sequence `x * log n + log n! - ∑ (m : ℕ) in finset.range (n + 1), log (x + m)`
  tends to `log Γ(x)` as `n → ∞`.
* the Bohr-Mollerup theorem (`real.eq_Gamma_of_log_convex`) which states that `Γ` is the unique
  *log-convex*, positive-real-valued function on the positive reals satisfying
  `f (x + 1) = x f x` and `f 1 = 1`.

To do this, we prove that any function satisfying the hypotheses of the Bohr--Mollerup theorem must
agree with the limit in the Euler limit formula, so there is at most one such function. Then we
show that `Γ` satisfies these conditions.

Since most of the auxiliary lemmas for the Bohr-Mollerup theorem are of no relevance outside the
context of this proof, we place them in a separate namespace `real.bohr_mollerup` to avoid clutter.
(This includes the logarithmic form of the Euler limit formula, since later we will prove a more
general form of the Euler limit formula valid for any real or complex `x`; see
`real.Gamma_seq_tendsto_Gamma` and `complex.Gamma_seq_tendsto_Gamma`.)
-/

namespace bohr_mollerup

/-- The function `n ↦ x log n + log n! - (log x + ... + log (x + n))`, which we will show tends to
`log (Gamma x)` as `n → ∞`. -/
def log_gamma_seq (x : ℝ) (n : ℕ) : ℝ :=
x * log n + log n! - ∑ (m : ℕ) in finset.range (n + 1), log (x + m)

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

lemma tendsto_log_Gamma {x : ℝ} (hx : 0 < x) :
  tendsto (log_gamma_seq x) at_top (𝓝 $ log (Gamma x)) :=
begin
  have : log (Gamma x) = (log ∘ Gamma) x - (log ∘ Gamma) 1,
  { simp_rw [function.comp_app, Gamma_one, log_one, sub_zero] },
  rw this,
  refine bohr_mollerup.tendsto_log_gamma_seq convex_on_log_Gamma (λ y hy, _) hx,
  rw [function.comp_app, Gamma_add_one hy.ne', log_mul hy.ne' (Gamma_pos_of_pos hy).ne', add_comm],
end

end bohr_mollerup -- (namespace)

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
    exact tendsto_nhds_unique e1 (bohr_mollerup.tendsto_log_Gamma hx) },
  { intros y hy,
    rw [function.comp_app, hf_feq hy, log_mul hy.ne' (hf_pos hy).ne'],
    ring }
end

end bohr_mollerup -- (section)

section strict_mono

lemma Gamma_two : Gamma 2 = 1 := by simpa using Gamma_nat_eq_factorial 1

lemma Gamma_three_div_two_lt_one : Gamma (3 / 2) < 1 :=
begin
  -- This can also be proved using the closed-form evaluation of `Gamma (1 / 2)` in
  -- `analysis.special_functions.gaussian`, but we give a self-contained proof using log-convexity
  -- to avoid unnecessary imports.
  have A : (0:ℝ) < 3/2, by norm_num,
  have := bohr_mollerup.f_add_nat_le convex_on_log_Gamma (λ y hy, _) two_ne_zero one_half_pos
    (by norm_num : 1/2 ≤ (1:ℝ)),
  swap, { rw [function.comp_app, Gamma_add_one hy.ne', log_mul hy.ne' (Gamma_pos_of_pos hy).ne',
    add_comm] },
  rw [function.comp_app, function.comp_app, nat.cast_two, Gamma_two, log_one, zero_add,
    (by norm_num : (2:ℝ) + 1/2 = 3/2 + 1), Gamma_add_one A.ne',
    log_mul A.ne' (Gamma_pos_of_pos A).ne', ←le_sub_iff_add_le',
    log_le_iff_le_exp (Gamma_pos_of_pos A)] at this,
  refine this.trans_lt (exp_lt_one_iff.mpr _),
  rw [mul_comm, ←mul_div_assoc, div_sub' _ _ (2:ℝ) two_ne_zero],
  refine div_neg_of_neg_of_pos _ two_pos,
  rw [sub_neg, mul_one, ←nat.cast_two, ←log_pow, ←exp_lt_exp, nat.cast_two, exp_log two_pos,
    exp_log];
  norm_num,
end

lemma Gamma_strict_mono_on_Ici : strict_mono_on Gamma (Ici 2) :=
begin
  convert convex_on_Gamma.strict_mono_of_lt (by norm_num : (0:ℝ) < 3/2)
    (by norm_num : (3/2 : ℝ) < 2) (Gamma_two.symm ▸ Gamma_three_div_two_lt_one),
  symmetry,
  rw inter_eq_right_iff_subset,
  exact λ x hx, two_pos.trans_le hx,
end

end strict_mono

end real

section beta_integral

/-! ## The Beta function -/

namespace complex

notation `cexp` := complex.exp

/-- The Beta function `Β (u, v)`, defined as `∫ x:ℝ in 0..1, x ^ (u - 1) * (1 - x) ^ (v - 1)`. -/
noncomputable def beta_integral (u v : ℂ) : ℂ :=
∫ (x:ℝ) in 0..1, x ^ (u - 1) * (1 - x) ^ (v - 1)

/-- Auxiliary lemma for `beta_integral_convergent`, showing convergence at the left endpoint. -/
lemma beta_integral_convergent_left {u : ℂ} (hu : 0 < re u) (v : ℂ) :
  interval_integrable (λ x, x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ → ℂ) volume 0 (1 / 2) :=
begin
  apply interval_integrable.mul_continuous_on,
  { refine interval_integral.interval_integrable_cpow' _,
    rwa [sub_re, one_re, ←zero_sub, sub_lt_sub_iff_right] },
  { apply continuous_at.continuous_on,
    intros x hx,
    rw uIcc_of_le (by positivity: (0:ℝ) ≤ 1/2) at hx,
    apply continuous_at.cpow,
    { exact (continuous_const.sub continuous_of_real).continuous_at },
    { exact continuous_at_const },
    { rw [sub_re, one_re, of_real_re, sub_pos],
      exact or.inl (hx.2.trans_lt (by norm_num : (1/2:ℝ) < 1)) } }
end

/-- The Beta integral is convergent for all `u, v` of positive real part. -/
lemma beta_integral_convergent {u v : ℂ} (hu : 0 < re u) (hv : 0 < re v) :
  interval_integrable (λ x, x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ → ℂ) volume 0 1 :=
begin
  refine (beta_integral_convergent_left hu v).trans _,
  rw interval_integrable.iff_comp_neg,
  convert ((beta_integral_convergent_left hv u).comp_add_right 1).symm,
  { ext1 x,
    conv_lhs { rw mul_comm },
    congr' 2;
    { push_cast, ring } },
  { norm_num },
  { norm_num }
end

lemma beta_integral_symm (u v : ℂ) :
  beta_integral v u = beta_integral u v :=
begin
  rw [beta_integral, beta_integral],
  have := interval_integral.integral_comp_mul_add
    (λ x:ℝ, (x:ℂ) ^ (u - 1) * (1 - ↑x) ^ (v - 1)) (neg_one_lt_zero.ne) 1,
  rw [inv_neg, inv_one, neg_one_smul, ←interval_integral.integral_symm] at this,
  convert this,
  { ext1 x, rw mul_comm, congr;
    { push_cast, ring } },
  { ring }, { ring }
end

lemma beta_integral_eval_one_right {u : ℂ} (hu : 0 < re u) :
  beta_integral u 1 = 1 / u :=
begin
  simp_rw [beta_integral, sub_self, cpow_zero, mul_one],
  rw integral_cpow (or.inl _),
  { rw [of_real_zero, of_real_one, one_cpow, zero_cpow,
    sub_zero, sub_add_cancel],
    rw sub_add_cancel,
    contrapose! hu, rw [hu, zero_re] },
  { rwa [sub_re, one_re, ←sub_pos, sub_neg_eq_add, sub_add_cancel] },
end

lemma beta_integral_scaled (s t : ℂ) {a : ℝ} (ha : 0 < a) :
  ∫ x in 0..a, (x:ℂ) ^ (s - 1) * (a - x) ^ (t - 1) = a ^ (s + t - 1) * beta_integral s t :=
begin
  have ha' : (a:ℂ) ≠ 0, from of_real_ne_zero.mpr ha.ne',
  rw beta_integral,
  have A : (a:ℂ) ^ (s + t - 1) = a * (a ^ (s - 1) * a ^ (t - 1)),
  { rw [(by abel : s + t - 1 = 1 + (s - 1) + (t - 1)),
      cpow_add _ _ ha', cpow_add 1 _ ha', cpow_one, mul_assoc] },
  rw [A, mul_assoc, ←interval_integral.integral_const_mul ((↑a) ^ _ * _),
    ←real_smul, ←(zero_div a), ←div_self ha.ne',
    ←interval_integral.integral_comp_div _ ha.ne', zero_div],
  simp_rw interval_integral.integral_of_le ha.le,
  refine set_integral_congr measurable_set_Ioc (λ x hx, _),
  dsimp only,
  rw mul_mul_mul_comm,
  congr' 1,
  { rw [←mul_cpow_of_real_nonneg ha.le (div_pos hx.1 ha).le, of_real_div, mul_div_cancel' _ ha'] },
  { rw [(by push_cast : (1:ℂ) - ↑(x / a) = ↑(1 - x / a)),
      ←mul_cpow_of_real_nonneg ha.le (sub_nonneg.mpr $ (div_le_one ha).mpr hx.2)],
    push_cast,
    rw [mul_sub, mul_one, mul_div_cancel' _ ha'] }
end

/-- Relation between Beta integral and Gamma function.  -/
lemma Gamma_mul_Gamma_eq_beta_integral {s t : ℂ} (hs : 0 < re s) (ht : 0 < re t) :
  Gamma s * Gamma t = Gamma (s + t) * beta_integral s t :=
begin
  -- Note that we haven't proved (yet) that the Gamma function has no zeroes, so we can't formulate
  -- this as a formula for the Beta function.
  have conv_int := integral_pos_convolution (Gamma_integral_convergent hs)
    (Gamma_integral_convergent ht) (continuous_linear_map.mul ℝ ℂ),
  simp_rw continuous_linear_map.mul_apply' at conv_int,
  have hst : 0 < re (s + t),
  { rw add_re, exact add_pos hs ht },
  rw [Gamma_eq_integral hs, Gamma_eq_integral ht, Gamma_eq_integral hst, Gamma_integral,
    Gamma_integral, Gamma_integral, ←conv_int, ←integral_mul_right (beta_integral _ _)],
  refine set_integral_congr measurable_set_Ioi (λ x hx, _),
  dsimp only,
  rw [mul_assoc, ←beta_integral_scaled s t hx, ←interval_integral.integral_const_mul],
  congr' 1 with y:1,
  push_cast,
  suffices : cexp (-x) = cexp (-y) * cexp (-(x - y)),
  { rw this, ring },
  { rw ←complex.exp_add, congr' 1, abel },
end

/-- Recurrence formula for the Beta function. -/
lemma beta_integral_recurrence {u v : ℂ} (hu : 0 < re u) (hv : 0 < re v) :
  u * beta_integral u (v + 1) = v * beta_integral (u + 1) v :=
begin
  -- NB: If we knew `Gamma (u + v + 1) ≠ 0` this would be an easy consequence of
  -- `Gamma_mul_Gamma_eq_beta_integral`; but we don't know that yet. We will prove it later, but
  -- this lemma is needed in the proof. So we give a (somewhat laborious) direct argument.
  let F : ℝ → ℂ := λ x, x ^ u * (1 - x) ^ v,
  have hu' : 0 < re (u + 1), by { rw [add_re, one_re], positivity },
  have hv' : 0 < re (v + 1), by { rw [add_re, one_re], positivity },
  have hc : continuous_on F (Icc 0 1),
  { refine (continuous_at.continuous_on (λ x hx, _)).mul (continuous_at.continuous_on (λ x hx, _)),
    { refine (continuous_at_cpow_const_of_re_pos (or.inl _) hu).comp
        continuous_of_real.continuous_at,
      rw of_real_re, exact hx.1 },
    { refine (continuous_at_cpow_const_of_re_pos (or.inl _) hv).comp
        (continuous_const.sub continuous_of_real).continuous_at,
      rw [sub_re, one_re, of_real_re, sub_nonneg],
      exact hx.2 } },
  have hder : ∀ (x : ℝ), x ∈ Ioo (0:ℝ) 1 → has_deriv_at F
    (u * (↑x ^ (u - 1) * (1 - ↑x) ^ v) - v * (↑x ^ u * (1 - ↑x) ^ (v - 1))) x,
  { intros x hx,
    have U : has_deriv_at (λ y:ℂ, y ^ u) (u * ↑x ^ (u - 1)) ↑x,
    { have := has_deriv_at.cpow_const (has_deriv_at_id ↑x) (or.inl _),
      { rw mul_one at this, exact this },
      { rw [id.def, of_real_re], exact hx.1 } },
    have V : has_deriv_at (λ y:ℂ, (1 - y) ^ v) (-v * (1 - ↑x) ^ (v - 1)) ↑x,
    { have A := has_deriv_at.cpow_const (has_deriv_at_id (1 - ↑x)) (or.inl _),
      rotate, { exact v },
      { rw [id.def, sub_re, one_re, of_real_re, sub_pos], exact hx.2 },
      simp_rw [id.def] at A,
      have B : has_deriv_at (λ y:ℂ, 1 - y) (-1) ↑x,
      { apply has_deriv_at.const_sub, apply has_deriv_at_id },
      convert has_deriv_at.comp ↑x A B using 1,
      ring },
    convert (U.mul V).comp_of_real,
    ring },
  have h_int := ((beta_integral_convergent hu hv').const_mul u).sub
    ((beta_integral_convergent hu' hv).const_mul v),
  dsimp only at h_int,
  rw [add_sub_cancel, add_sub_cancel] at h_int,
  have int_ev := interval_integral.integral_eq_sub_of_has_deriv_at_of_le zero_le_one hc hder h_int,
  have hF0 : F 0 = 0,
  { simp only [mul_eq_zero, of_real_zero, cpow_eq_zero_iff, eq_self_iff_true,
      ne.def, true_and, sub_zero, one_cpow, one_ne_zero, or_false],
    contrapose! hu, rw [hu, zero_re] },
  have hF1 : F 1 = 0,
  { simp only [mul_eq_zero, of_real_one, one_cpow, one_ne_zero, sub_self,
      cpow_eq_zero_iff, eq_self_iff_true, ne.def, true_and, false_or],
    contrapose! hv, rw [hv, zero_re] },
  rw [hF0, hF1, sub_zero, interval_integral.integral_sub,
    interval_integral.integral_const_mul, interval_integral.integral_const_mul] at int_ev,
  { rw [beta_integral, beta_integral, ←sub_eq_zero],
    convert int_ev;
    { ext1 x, congr, abel } },
  { apply interval_integrable.const_mul,
    convert beta_integral_convergent hu hv',
    ext1 x, rw add_sub_cancel },
  { apply interval_integrable.const_mul,
    convert beta_integral_convergent hu' hv,
    ext1 x, rw add_sub_cancel },
end

/-- Explicit formula for the Beta function when second argument is a positive integer. -/
lemma beta_integral_eval_nat_add_one_right {u : ℂ} (hu : 0 < re u) (n : ℕ) :
  beta_integral u (n + 1) = n! / ∏ (j:ℕ) in finset.range (n + 1), (u + j) :=
begin
  induction n with n IH generalizing u,
  { rw [nat.cast_zero, zero_add, beta_integral_eval_one_right hu,
      nat.factorial_zero, nat.cast_one, zero_add, finset.prod_range_one, nat.cast_zero, add_zero] },
  { have := beta_integral_recurrence hu (_ : 0 < re n.succ),
    swap, { rw [←of_real_nat_cast, of_real_re], positivity },
    rw [mul_comm u _, ←eq_div_iff] at this,
    swap, { contrapose! hu, rw [hu, zero_re] },
    rw [this, finset.prod_range_succ', nat.cast_succ, IH],
    swap, { rw [add_re, one_re], positivity },
    rw [nat.factorial_succ, nat.cast_mul, nat.cast_add, nat.cast_one, nat.cast_zero, add_zero,
      ←mul_div_assoc, ←div_div],
    congr' 3 with j:1,
    push_cast, abel }
end

end complex

end beta_integral

section limit_formula

/-! ## The Euler limit formula -/

namespace complex

/-- The sequence with `n`-th term `n ^ s * n! / (s * (s + 1) * ... * (s + n))`, for complex `s`.
We will show that this tends to `Γ(s)` as `n → ∞`. -/
noncomputable def Gamma_seq (s : ℂ) (n : ℕ) :=
(n:ℂ) ^ s * n! / ∏ (j:ℕ) in finset.range (n + 1), (s + j)

lemma Gamma_seq_eq_beta_integral_of_re_pos {s : ℂ} (hs : 0 < re s) (n : ℕ) :
  Gamma_seq s n = n ^ s * beta_integral s (n + 1) :=
by rw [Gamma_seq, beta_integral_eval_nat_add_one_right hs n, ←mul_div_assoc]

lemma Gamma_seq_add_one_left (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
  (Gamma_seq (s + 1) n) / s = n / (n + 1 + s) * Gamma_seq s n :=
begin
  conv_lhs { rw [Gamma_seq, finset.prod_range_succ, div_div] },
  conv_rhs { rw [Gamma_seq, finset.prod_range_succ', nat.cast_zero, add_zero, div_mul_div_comm,
    ←mul_assoc, ←mul_assoc, mul_comm _ (finset.prod _ _)] },
  congr' 3,
  { rw [cpow_add _ _ (nat.cast_ne_zero.mpr hn), cpow_one, mul_comm] },
  { refine finset.prod_congr (by refl) (λ x hx, _),
    push_cast, ring },
  { abel }
end

lemma Gamma_seq_eq_approx_Gamma_integral {s : ℂ} (hs : 0 < re s) {n : ℕ} (hn : n ≠ 0) :
  Gamma_seq s n = ∫ x:ℝ in 0..n, ↑((1 - x / n) ^ n) * (x:ℂ) ^ (s - 1) :=
begin
  have : ∀ (x : ℝ), x = x / n * n, by { intro x, rw div_mul_cancel, exact nat.cast_ne_zero.mpr hn },
  conv in (↑_ ^ _) { congr, rw this x },
  rw Gamma_seq_eq_beta_integral_of_re_pos hs,
  rw [beta_integral, @interval_integral.integral_comp_div _ _ _ _ 0 n _
    (λ x, ↑((1 - x) ^ n) * ↑(x * ↑n) ^ (s - 1) : ℝ → ℂ) (nat.cast_ne_zero.mpr hn),
    real_smul, zero_div, div_self, add_sub_cancel, ←interval_integral.integral_const_mul,
    ←interval_integral.integral_const_mul],
  swap, { exact nat.cast_ne_zero.mpr hn },
  simp_rw interval_integral.integral_of_le zero_le_one,
  refine set_integral_congr measurable_set_Ioc (λ x hx, _),
  push_cast,
  have hn' : (n : ℂ) ≠ 0, from nat.cast_ne_zero.mpr hn,
  have A : (n : ℂ) ^ s = (n : ℂ) ^ (s - 1)  * n,
  { conv_lhs { rw [(by ring : s = (s - 1) + 1), cpow_add _ _ hn'] },
    simp },
  have B : ((x : ℂ) * ↑n) ^ (s - 1) = (x : ℂ) ^ (s - 1) * ↑n ^ (s - 1),
  { rw [←of_real_nat_cast,
      mul_cpow_of_real_nonneg hx.1.le (nat.cast_pos.mpr (nat.pos_of_ne_zero hn)).le] },
  rw [A, B, cpow_nat_cast], ring,
end

/-- The main techical lemma for `Gamma_seq_tendsto_Gamma`, expressing the integral defining the
Gamma function for `0 < re s` as the limit of a sequence of integrals over finite intervals. -/
lemma approx_Gamma_integral_tendsto_Gamma_integral {s : ℂ} (hs : 0 < re s) :
  tendsto (λ n:ℕ, ∫ x:ℝ in 0..n, ↑((1 - x / n) ^ n) * (x:ℂ) ^ (s - 1)) at_top (𝓝 $ Gamma s) :=
begin
  rw [Gamma_eq_integral hs],
  -- We apply dominated convergence to the following function, which we will show is uniformly
  -- bounded above by the Gamma integrand `exp (-x) * x ^ (re s - 1)`.
  let f : ℕ → ℝ → ℂ := λ n, indicator (Ioc 0 (n:ℝ))
    (λ x:ℝ, ↑((1 - x / n) ^ n) * (x:ℂ) ^ (s - 1)),
  -- integrability of f
  have f_ible : ∀ (n:ℕ), integrable (f n) (volume.restrict (Ioi 0)),
  { intro n,
    rw [integrable_indicator_iff (measurable_set_Ioc : measurable_set (Ioc (_:ℝ) _)),
      integrable_on, measure.restrict_restrict_of_subset Ioc_subset_Ioi_self, ←integrable_on,
      ←interval_integrable_iff_integrable_Ioc_of_le (by positivity : (0:ℝ) ≤ n)],
    apply interval_integrable.continuous_on_mul,
    { refine interval_integral.interval_integrable_cpow' _,
      rwa [sub_re, one_re, ←zero_sub, sub_lt_sub_iff_right] },
    { apply continuous.continuous_on, continuity } },
  -- pointwise limit of f
  have f_tends : ∀ x:ℝ, x ∈ Ioi (0:ℝ) →
    tendsto (λ n:ℕ, f n x) at_top (𝓝 $ ↑(real.exp (-x)) * (x:ℂ) ^ (s - 1)),
  { intros x hx,
    apply tendsto.congr',
    show ∀ᶠ n:ℕ in at_top, ↑((1 - x / n) ^ n) * (x:ℂ) ^ (s - 1) = f n x,
    { refine eventually.mp (eventually_ge_at_top ⌈x⌉₊) (eventually_of_forall (λ n hn, _)),
      rw nat.ceil_le at hn,
      dsimp only [f],
      rw indicator_of_mem,
      exact ⟨hx, hn⟩ },
    { simp_rw mul_comm _ (↑x ^ _),
      refine (tendsto.comp (continuous_of_real.tendsto _) _).const_mul _,
      convert tendsto_one_plus_div_pow_exp (-x),
      ext1 n,
      rw [neg_div, ←sub_eq_add_neg] } },
  -- let `convert` identify the remaining goals
  convert tendsto_integral_of_dominated_convergence _ (λ n, (f_ible n).1)
    (real.Gamma_integral_convergent hs) _
    ((ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ f_tends)),
  -- limit of f is the integrand we want
  { ext1 n,
    rw [integral_indicator (measurable_set_Ioc : measurable_set (Ioc (_:ℝ) _)),
      interval_integral.integral_of_le (by positivity: 0 ≤ (n:ℝ)),
      measure.restrict_restrict_of_subset Ioc_subset_Ioi_self] },
  -- f is uniformly bounded by the Gamma integrand
  { intro n,
    refine (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ (λ x hx, _)),
    dsimp only [f],
    rcases lt_or_le (n:ℝ) x with hxn | hxn,
    { rw [indicator_of_not_mem (not_mem_Ioc_of_gt hxn), norm_zero,
        mul_nonneg_iff_right_nonneg_of_pos (exp_pos _)],
      exact rpow_nonneg_of_nonneg (le_of_lt hx) _ },
    { rw [indicator_of_mem (mem_Ioc.mpr ⟨hx, hxn⟩), norm_mul, complex.norm_eq_abs,
        complex.abs_of_nonneg
          (pow_nonneg (sub_nonneg.mpr $ div_le_one_of_le hxn $ by positivity) _),
        complex.norm_eq_abs, abs_cpow_eq_rpow_re_of_pos hx, sub_re, one_re,
        mul_le_mul_right (rpow_pos_of_pos hx _ )],
      exact one_sub_div_pow_le_exp_neg hxn } }
end

/-- Euler's limit formula for the complex Gamma function. -/
lemma Gamma_seq_tendsto_Gamma (s : ℂ) :
  tendsto (Gamma_seq s) at_top (𝓝 $ Gamma s) :=
begin
  suffices : ∀ m : ℕ, (-↑m < re s) → tendsto (Gamma_seq s) at_top (𝓝 $ Gamma_aux m s),
  { rw Gamma,
    apply this,
    rw neg_lt,
    rcases lt_or_le 0 (re s) with hs | hs,
    { exact (neg_neg_of_pos hs).trans_le (nat.cast_nonneg _), },
    { refine (nat.lt_floor_add_one _).trans_le _,
      rw [sub_eq_neg_add, nat.floor_add_one (neg_nonneg.mpr hs), nat.cast_add_one] } },
  intro m,
  induction m with m IH generalizing s,
  { -- Base case: `0 < re s`, so Gamma is given by the integral formula
    intro hs,
    rw [nat.cast_zero, neg_zero] at hs,
    rw [←Gamma_eq_Gamma_aux],
    { refine tendsto.congr' _ (approx_Gamma_integral_tendsto_Gamma_integral hs),
      refine (eventually_ne_at_top 0).mp (eventually_of_forall (λ n hn, _)),
      exact (Gamma_seq_eq_approx_Gamma_integral hs hn).symm },
    { rwa [nat.cast_zero, neg_lt_zero] } },
  { -- Induction step: use recurrence formulae in `s` for Gamma and Gamma_seq
    intro hs,
    rw [nat.cast_succ, neg_add, ←sub_eq_add_neg, sub_lt_iff_lt_add, ←one_re, ←add_re] at hs,
    rw Gamma_aux,
    have := tendsto.congr' ((eventually_ne_at_top 0).mp (eventually_of_forall (λ n hn, _)))
      ((IH _ hs).div_const s),
    swap 3, { exact Gamma_seq_add_one_left s hn }, -- doesn't work if inlined?
    conv at this in (_ / _ * _) { rw mul_comm },
    rwa [←mul_one (Gamma_aux m (s + 1) / s), tendsto_mul_iff_of_ne_zero _ (one_ne_zero' ℂ)] at this,
    simp_rw add_assoc,
    exact tendsto_coe_nat_div_add_at_top (1 + s) }
end

end complex

end limit_formula

section gamma_reflection
/-! ## The reflection formula -/

open_locale real
namespace complex

lemma Gamma_seq_mul (z : ℂ) {n : ℕ} (hn : n ≠ 0) :
  Gamma_seq z n * Gamma_seq (1 - z) n =
  n / (n + 1 - z) * (1 / (z * ∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2))) :=
begin
  -- also true for n = 0 but we don't need it
  have aux : ∀ (a b c d : ℂ), a * b * (c * d) = a * c * (b * d), by { intros, ring },
  rw [Gamma_seq, Gamma_seq, div_mul_div_comm, aux, ←pow_two],
  have : (n : ℂ) ^ z * n ^ (1 - z) = n,
  { rw [←cpow_add _ _ (nat.cast_ne_zero.mpr hn), add_sub_cancel'_right, cpow_one] },
  rw [this, finset.prod_range_succ', finset.prod_range_succ, aux, ←finset.prod_mul_distrib,
    nat.cast_zero, add_zero, add_comm (1 - z) n, ←add_sub_assoc],
  have : ∀ (j : ℕ), (z + ↑(j + 1)) * (1 - z + ↑j) = ↑((j + 1) ^ 2) * (1 - z ^ 2 / (↑j + 1) ^ 2),
  { intro j,
    push_cast,
    have : (j:ℂ) + 1 ≠ 0, by { rw [←nat.cast_succ, nat.cast_ne_zero], exact nat.succ_ne_zero j },
    field_simp, ring },
  simp_rw this,
  rw [finset.prod_mul_distrib, ←nat.cast_prod, finset.prod_pow,
    finset.prod_range_add_one_eq_factorial, nat.cast_pow,
    (by {intros, ring} : ∀ (a b c d : ℂ), a * b * (c * d) = a * (d * (b * c))),
    ←div_div, mul_div_cancel, ←div_div, mul_comm z _, mul_one_div],
  exact pow_ne_zero 2 (nat.cast_ne_zero.mpr $ nat.factorial_ne_zero n),
end

/-- Euler's reflection formula for the complex Gamma function. -/
theorem Gamma_mul_Gamma_one_sub (z : ℂ) : Gamma z * Gamma (1 - z) = π / sin (π * z) :=
begin
  have pi_ne : (π : ℂ) ≠ 0, from complex.of_real_ne_zero.mpr pi_ne_zero,
  by_cases hs : sin (↑π * z) = 0,
  { -- first deal with silly case z = integer
    rw [hs, div_zero],
    rw [←neg_eq_zero, ←complex.sin_neg, ←mul_neg, complex.sin_eq_zero_iff, mul_comm] at hs,
    obtain ⟨k, hk⟩ := hs,
    rw [mul_eq_mul_right_iff, eq_false_intro (of_real_ne_zero.mpr pi_pos.ne'), or_false,
      neg_eq_iff_eq_neg] at hk,
    rw hk,
    cases k,
    { rw [int.cast_of_nat, complex.Gamma_neg_nat_eq_zero, zero_mul] },
    { rw [int.cast_neg_succ_of_nat, neg_neg, nat.cast_add, nat.cast_one, add_comm, sub_add_cancel',
        complex.Gamma_neg_nat_eq_zero, mul_zero] } },
  refine tendsto_nhds_unique ((Gamma_seq_tendsto_Gamma z).mul (Gamma_seq_tendsto_Gamma $ 1 - z)) _,
  have : ↑π / sin (↑π * z) = 1 * (π / sin (π * z)), by rw one_mul, rw this,
  refine tendsto.congr' ((eventually_ne_at_top 0).mp
    (eventually_of_forall (λ n hn, (Gamma_seq_mul z hn).symm))) (tendsto.mul _ _),
  { convert tendsto_coe_nat_div_add_at_top (1 - z), ext1 n, rw add_sub_assoc },
  { have : ↑π / sin (↑π * z) = 1 / (sin (π * z) / π), by field_simp, rw this,
    refine tendsto_const_nhds.div _ (div_ne_zero hs pi_ne),
    rw [←tendsto_mul_iff_of_ne_zero tendsto_const_nhds pi_ne, div_mul_cancel _ pi_ne],
    convert tendsto_euler_sin_prod z,
    ext1 n, rw [mul_comm, ←mul_assoc] },
end

/-- The Gamma function does not vanish on `ℂ` (except at non-positive integers, where the function
is mathematically undefined and we set it to `0` by convention). -/
theorem Gamma_ne_zero {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) : Gamma s ≠ 0 :=
begin
  by_cases h_im : s.im = 0,
  { have : s = ↑s.re,
    { conv_lhs { rw ←complex.re_add_im s }, rw [h_im, of_real_zero, zero_mul, add_zero] },
    rw [this, Gamma_of_real, of_real_ne_zero],
    refine real.Gamma_ne_zero (λ n, _),
    specialize hs n,
    contrapose! hs,
    rwa [this, ←of_real_nat_cast, ←of_real_neg, of_real_inj] },
  { have : sin (↑π * s) ≠ 0,
    { rw complex.sin_ne_zero_iff,
      intro k,
      apply_fun im,
      rw [of_real_mul_im, ←of_real_int_cast, ←of_real_mul, of_real_im],
      exact mul_ne_zero real.pi_pos.ne' h_im },
    have A := div_ne_zero (of_real_ne_zero.mpr real.pi_pos.ne') this,
    rw [←complex.Gamma_mul_Gamma_one_sub s, mul_ne_zero_iff] at A,
    exact A.1 }
end

lemma Gamma_eq_zero_iff (s : ℂ) : Gamma s = 0 ↔ ∃ m : ℕ, s = -m :=
begin
  split,
  { contrapose!, exact Gamma_ne_zero },
  { rintro ⟨m, rfl⟩, exact Gamma_neg_nat_eq_zero m },
end

end complex

namespace real

/-- The sequence with `n`-th term `n ^ s * n! / (s * (s + 1) * ... * (s + n))`, for real `s`. We
will show that this tends to `Γ(s)` as `n → ∞`. -/
noncomputable def Gamma_seq (s : ℝ) (n : ℕ) :=
(n : ℝ) ^ s * n! / ∏ (j : ℕ) in finset.range (n + 1), (s + j)

/-- Euler's limit formula for the real Gamma function. -/
lemma Gamma_seq_tendsto_Gamma (s : ℝ) : tendsto (Gamma_seq s) at_top (𝓝 $ Gamma s) :=
begin
  suffices : tendsto (coe ∘ Gamma_seq s : ℕ → ℂ) at_top (𝓝 $ complex.Gamma s),
    from (complex.continuous_re.tendsto (complex.Gamma ↑s)).comp this,
  convert complex.Gamma_seq_tendsto_Gamma s,
  ext1 n,
  dsimp only [Gamma_seq, function.comp_app, complex.Gamma_seq],
  push_cast,
  rw [complex.of_real_cpow n.cast_nonneg, complex.of_real_nat_cast]
end

/-- Euler's reflection formula for the real Gamma function. -/
lemma Gamma_mul_Gamma_one_sub (s : ℝ) : Gamma s * Gamma (1 - s) = π / sin (π * s) :=
begin
  simp_rw [←complex.of_real_inj, complex.of_real_div, complex.of_real_sin,
    complex.of_real_mul, ←complex.Gamma_of_real, complex.of_real_sub, complex.of_real_one],
  exact complex.Gamma_mul_Gamma_one_sub s
end

end real

end gamma_reflection
