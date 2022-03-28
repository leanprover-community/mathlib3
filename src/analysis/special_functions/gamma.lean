/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import measure_theory.integral.exp_decay
import analysis.calculus.parametric_integral

/-!
# The Gamma function

This file defines the `Γ` function (for a real or complex variable `s`). This is defined
using Euler's integral `∫ x in Ioi 0, exp (-x) * x ^ (s - 1)` where we can prove its
convergence -- for `1 ≤ s` in the real case, and `1 ≤ re s` in the complex case -- and
extending it to the whole of `ℂ` using the recurrence `Γ(s + 1) = s Γ(s)`.

The main results are:

- definition of `gamma : ℂ → ℂ`
- `gamma_recurrence`: we have `gamma (s+1) = s * gamma s` for all `s ∈ ℂ` with `s ≠ 0`.
- `gamma_integer_eq_factorial`: for all `n ∈ ℕ` we have `gamma (n+1) = factorial n`
- `differentiable_at_gamma`: the gamma function is differentiable (as a complex function)
  at any `s ∈ ℂ` with `s + m ≠ 0 ∀ m ∈ ℕ`.

## Tags

gamma
-/

noncomputable theory
open filter interval_integral set real measure_theory
open_locale topological_space

section gamma_real

/-- Asymptotic bound for the Γ function integrand. -/
lemma gamma_integrand_is_O (s : ℝ) : asymptotics.is_O (λ x:ℝ, exp (-x) * x ^ s)
  (λ x:ℝ, exp (-(1/2) * x)) at_top :=
begin
  refine asymptotics.is_o.is_O (asymptotics.is_o_of_tendsto _ _),
  { intros x hx, exfalso, exact (exp_pos (-(1 / 2) * x)).ne' hx },
  have : (λ (x:ℝ), exp (-x) * x ^ s / exp (-(1 / 2) * x)) = (λ (x:ℝ), exp ((1 / 2) * x) / x ^ s )⁻¹,
  { ext1 x, dsimp,
    have : exp (-x) = exp (-(1 / 2) * x) * exp (-(1 / 2) * x),
    { rw ←real.exp_add, field_simp },
    rw this,
    have : exp (1 / 2 * x) = (exp (-(1 / 2) * x))⁻¹ := by { rw ←exp_neg, field_simp, },
    rw this,
    field_simp [(exp_pos (-x/2)).ne'], ring },
  rw this,
  exact (tendsto_exp_mul_div_rpow_at_top s (1 / 2) one_half_pos).inv_tendsto_at_top,
end

/-- Euler's integral for the `Γ` function (of a real variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `gamma_real_integral_convergent` for a proof of the convergence of the integral for `1 ≤ s`. -/
def gamma_real_integral (s : ℝ) : ℝ := ∫ x in Ioi (0:ℝ), exp (-x) * x ^ (s - 1)

/-- The integral defining the Γ function converges for real `s` with `1 ≤ s`.

This is not optimal, but the optimal bound (convergence for `0 < s`) is hard to establish with the
results currently in the library. -/
lemma gamma_real_integral_convergent {s : ℝ} (h : 1 ≤ s) : integrable_on
  (λ x:ℝ, exp (-x) * x ^ (s - 1)) (Ioi 0) :=
begin
  refine integrable_of_is_O_exp_neg one_half_pos _ (gamma_integrand_is_O _ ),
  refine continuous_on_id.neg.exp.mul (continuous_on_id.rpow_const _),
  intros x hx, right, simpa only [sub_nonneg] using h,
end

/- Most of this is just showing `∫ x in Ioi 0, exp (-x) = 1` -- maybe this should go elsewhere? -/
lemma gamma_real_integral_one : gamma_real_integral 1 = 1 :=
begin
  have : ∫ (x : ℝ) in Ioi 0, exp (-x) * x ^ (0:ℝ) = ∫ (x : ℝ) in Ioi 0, exp (-x),
  { congr, ext1, rw [rpow_zero, mul_one], },
  rw [gamma_real_integral, sub_self, this],
  have t1: tendsto (λ X:ℝ, ∫ x in 0..X, exp (-x)) at_top (𝓝 1),
  { simp only [integral_comp_neg, neg_zero, integral_exp, real.exp_zero],
    simpa only [sub_zero] using tendsto_exp_neg_at_top_nhds_0.const_sub 1, },
  refine tendsto_nhds_unique (interval_integral_tendsto_integral_Ioi _ _ tendsto_id) t1,
  simpa only [neg_mul, one_mul] using exp_neg_integrable_on_Ioi 0 zero_lt_one,
end

end gamma_real

section gamma_complex

open complex

lemma abs_cpow_of_pos_real (s : ℂ) {x : ℝ} (hx : 0 < x) : complex.abs (x ^ s)  = x ^ (s.re) :=
begin
  rw cpow_def_of_ne_zero,
  { rw [complex.abs_exp, ←of_real_log hx.le, of_real_mul_re, exp_mul, exp_log hx],},
  { rwa [ne.def, of_real_eq_zero, ←ne.def], exact hx.ne',}
end

/-- The integral defining the Γ function converges for complex `s` with `1 ≤ re s`.

This is proved by reduction to the real case. The bound is not optimal, but the optimal bound
(convergence for `0 < re s`) is hard to establish with the results currently in the library. -/
lemma gamma_complex_integral_convergent {s : ℂ} (hs : 1 ≤ s.re) :
  integrable_on (λ x:ℝ, real.exp (-x) * x ^ (s - 1) : ℝ → ℂ) (Ioi 0) :=
begin
  -- This is slightly subtle if `s` is non-real but `s.re = 1`, as the integrand is not continuous
  -- at the lower endpoint. However, it is continuous on the interior, and its norm is continuous
  -- at the endpoint, which is good enough.
  split,
  { refine continuous_on.ae_measurable _ measurable_set_Ioi,
    apply (continuous_of_real.comp continuous_neg.exp).continuous_on.mul,
    apply continuous_at.continuous_on,
    intros x hx,
    have : continuous_at (λ x:ℂ, x ^ (s - 1)) ↑x,
    { apply continuous_at_cpow_const, rw of_real_re, exact or.inl hx, },
    exact continuous_at.comp this continuous_of_real.continuous_at },
  { rw ←has_finite_integral_norm_iff,
    refine has_finite_integral.congr (gamma_real_integral_convergent hs).2 _,
    refine (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ (λ x hx, _)),
    dsimp only,
    rw [complex.norm_eq_abs, complex.abs_mul, complex.abs_of_nonneg $ le_of_lt $ exp_pos $ -x,
      abs_cpow_of_pos_real _ hx],
    simp }
end

/-- Euler's integral for the `Γ` function (of a complex variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `gamma_complex_integral_convergent` for a proof of the convergence of the integral for
`1 ≤ re s`. -/
def gamma_complex_integral (s : ℂ) : ℂ := ∫ x in Ioi (0:ℝ), ↑(exp (-x)) * ↑x ^ (s - 1)

lemma gamma_complex_integral_of_real (s : ℝ) :
  gamma_complex_integral ↑s = ↑(gamma_real_integral s) :=
begin
  rw [gamma_real_integral, ←integral_of_real],
  refine set_integral_congr measurable_set_Ioi _,
  intros x hx, dsimp only,
  rw [of_real_mul, of_real_cpow (mem_Ioi.mp hx).le],
  simp,
end

lemma gamma_complex_integral_one : gamma_complex_integral 1 = 1 :=
begin
  rw [←of_real_one, gamma_complex_integral_of_real 1, of_real_inj],
  exact gamma_real_integral_one,
end

end gamma_complex


section gamma_integral_recurrence

/- First some tedious lemmas about functions ℝ → ℂ -/

lemma abs_cpow_of_real {s : ℂ} {x : ℝ} (hs: 0 < s.re) (hx : 0 ≤ x):
  complex.abs( ↑x ^ s ) = x ^ (s.re) :=
begin
  rw complex.cpow_def, split_ifs,
  { rw h_1, simp, },
  { rw complex.of_real_eq_zero at h, rw [h, complex.abs_zero, zero_rpow hs.ne'] },
  { have : 0 < x,
    { simp only [complex.of_real_eq_zero] at h,
      exact lt_of_le_of_ne hx ( ne_comm.mp h ) , },
    have t:= abs_cpow_of_pos_real s this,
    rw complex.cpow_def_of_ne_zero (complex.of_real_ne_zero.mpr this.ne') at t,
    exact t }
end

/- This is not a special case of continuous_at_cpow_const, since here we get continuity on a
larger domain (including 0) at the cost of stronger hypotheses on the exponent. -/
lemma cts_cpow {s : ℂ} (hs: 0 < s.re): continuous_on (λ x, ↑x ^ s : ℝ → ℂ) (Ici 0) :=
begin
  -- There must be a better way of doing this.
  intros x hx,
  by_cases 0 < x,
  { apply continuous_at.continuous_within_at,
    refine (_ : continuous_at (λ x:ℂ, x^s) ↑x).comp complex.continuous_of_real.continuous_at,
    apply continuous_at_cpow_const, rw complex.of_real_re, exact or.inl h },
  rw mem_Ici at hx,
  have : x = 0 := by { linarith }, rw this,
  have hs2 : s ≠ 0 := by { contrapose! hs, rw [hs, complex.zero_re], },
  rw continuous_within_at,
  have : (↑(0:ℝ))^s = (0:ℂ) := by { rw complex.of_real_zero, exact complex.zero_cpow hs2 },
  rw [this, tendsto_zero_iff_norm_tendsto_zero],
  have u: eq_on (λ (e : ℝ), e ^ s.re)  (λ (e : ℝ), complex.abs(↑e ^ s)) (Ici 0),
  { intros y hy, symmetry, exact abs_cpow_of_real hs hy },
  have w: tendsto (λ (e : ℝ), e ^ s.re) (𝓝[Ici 0] 0) (𝓝 (0^s.re)),
  { exact tendsto.rpow_const continuous_within_at_id (or.inr hs.le), },
  rw zero_rpow hs.ne' at w,
  exact tendsto.congr' (eventually_nhds_within_of_forall u) w,
end

lemma has_deriv_at_coe (t: ℝ): has_deriv_at (coe: ℝ → ℂ) 1 t :=
begin
  rw has_deriv_at_iff_tendsto,
  simp only [complex.real_smul, complex.of_real_sub, mul_one, sub_self, complex.norm_eq_abs,
    complex.abs_zero, mul_zero],
  exact tendsto_const_nhds,
end

lemma has_deriv_at_of_real {f : ℝ → ℝ} {d x: ℝ} (hf: has_deriv_at f d x):
  (has_deriv_at ( (coe ∘ f) : ℝ → ℂ) ↑d x) :=
begin
  simpa using has_deriv_at.scomp x (has_deriv_at_coe $ f x ) hf
end

/-- Actual work starts here -/

lemma cont_integrand {s : ℂ} (hs: 0 < s.re):
  continuous_on (λ x, exp(-x) * x^s : ℝ → ℂ) (Ici 0) :=
begin
  apply (continuous.comp complex.continuous_of_real continuous_neg.exp).continuous_on.mul,
  exact cts_cpow hs,
end

lemma cont_integrand' {s : ℂ} :
  continuous_on (λ x, exp(-x) * x^s : ℝ → ℂ) (Ioi 0) :=
begin
  apply (continuous.comp complex.continuous_of_real continuous_neg.exp).continuous_on.mul,
  apply continuous_at.continuous_on, intros x hx,
  suffices: continuous_at (λ z:ℂ, z^s ) ↑x,
  { exact continuous_at.comp this complex.continuous_of_real.continuous_at },
  apply continuous_at_cpow_const, rw complex.of_real_re, exact or.inl hx,
end

lemma deriv_integrand (s : ℂ) {x : ℝ} (h1: 0 < x) : has_deriv_at  (λ x, exp(-x) * x^s : ℝ → ℂ)
(- (exp (-x) * x ^ s) + exp (-x) * (s * x ^ (s - 1))) x :=
begin
  have d1 : has_deriv_at (λ (y: ℝ), exp(-y)) (-exp(-x)) x,
  { simpa only [mul_neg, mul_one] using (has_deriv_at_neg x).exp },
  have d2: has_deriv_at (λ (y : ℝ), ↑y ^ s) (s * x ^ (s-1)) x,
  { have t := has_deriv_at.cpow_const (has_deriv_at_id ↑x),
    swap, exact s,
    simp only [id.def, complex.of_real_re, complex.of_real_im, ne.def,
       eq_self_iff_true, not_true, or_false, mul_one] at t,
    simpa only [mul_one] using has_deriv_at.comp _ (t h1) (has_deriv_at_coe x), },
  simpa only [complex.of_real_neg, neg_mul] using has_deriv_at.mul (has_deriv_at_of_real d1) d2,
end

/-- The indefinite version of the Γ function, Γ(s, X) = ∫ x ∈ 0..X, exp(-x) x^(s-1). -/
def partial_gamma (s : ℂ) (X : ℝ) : ℂ := ∫ x in 0..X, exp(-x) * x ^ (s - 1)

lemma gamma_integrand_interval_integrable (s : ℂ) {Y : ℝ} (hs: 1 ≤ s.re) (hY: 0 ≤ Y):
  interval_integrable (λ (x : ℝ),  ↑(exp (-x)) * ↑x ^ (s-1) : ℝ → ℂ) measure_space.volume 0 Y :=
begin
  rw interval_integrable_iff_integrable_Ioc_of_le hY,
  exact integrable_on.mono_set (gamma_complex_integral_convergent hs) Ioc_subset_Ioi_self
end

lemma deriv_interval_integrable_A {s : ℂ} (hs: 1 ≤ s.re) {Y : ℝ} (hY : 0 ≤ Y):
 interval_integrable (λ (x : ℝ), -(↑(exp (-x)) * ↑x ^ s) : ℝ → ℂ) measure_space.volume 0 Y :=
begin
  have t := (gamma_integrand_interval_integrable (s+1) _ hY).neg,
  { simpa only [add_sub_cancel] using t },
  { simp only [complex.add_re, complex.one_re], linarith,},
end

lemma deriv_interval_integrable_B {s : ℂ} (hs: 1 ≤ s.re) {Y : ℝ} (hY : 0 ≤ Y): interval_integrable
  (λ (x : ℝ), ↑(exp (-x)) * (s * ↑x ^ (s - 1)) : ℝ → ℂ) measure_space.volume 0 Y :=
begin
  have: (λ (x : ℝ), ↑(exp (-x)) * (s * ↑x ^ (s - 1))) =
    (λ (x : ℝ), s * (↑(exp (-x)) * ↑x ^ (s - 1))) := by { ext1, ring, },
  rw [this, interval_integrable_iff_integrable_Ioc_of_le hY],
  split,
  { refine continuous_on.ae_measurable (continuous_on_const.mul _) measurable_set_Ioc,
    apply (complex.continuous_of_real.comp continuous_neg.exp).continuous_on.mul,
    apply continuous_at.continuous_on,
    intros x hx,
    refine (_ : continuous_at (λ x:ℂ, x ^ (s - 1)) _).comp complex.continuous_of_real.continuous_at,
    apply continuous_at_cpow_const, rw complex.of_real_re, exact or.inl hx.1, },
  apply has_finite_integral_of_bounded, swap, exact s.abs * Y^(s.re - 1),
  refine (ae_restrict_iff' measurable_set_Ioc).mpr (ae_of_all _ (λ x hx, _)),
  rw [complex.norm_eq_abs, complex.abs_mul,complex.abs_mul, complex.abs_of_nonneg (exp_pos(-x)).le],
  apply mul_le_mul_of_nonneg_left, swap, exact complex.abs_nonneg s,
  have i1: exp (-x) ≤ 1 := by { simpa using hx.1.le, },
  have i2: complex.abs (↑x ^ (s - 1)) ≤ Y ^ (s.re - 1),
  { rw [abs_cpow_of_pos_real (s-1) hx.1, complex.sub_re, complex.one_re],
    apply rpow_le_rpow hx.1.le hx.2, linarith, },
  simpa using mul_le_mul i1 i2 (complex.abs_nonneg (↑x ^ (s - 1))) zero_le_one,
end

lemma partial_gamma_recurrence {s : ℂ} (hs: 1 ≤ s.re) {X : ℝ} (hX : 0 ≤ X) :
  partial_gamma (s+1) X = s * partial_gamma s X - exp(-X) * X^s :=
begin
  rw [partial_gamma, partial_gamma, add_sub_cancel],

  have F_der_I: (∀ (x:ℝ), (x ∈ Ioo 0 X) → has_deriv_at (λ x, exp(-x) * x ^ s : ℝ → ℂ)
    ( -(exp (-x) * x ^ s) + exp (-x) * (s * x ^ (s - 1))) x),
  { intros x hx, rw mem_Ioo at hx, exact deriv_integrand s hx.1 },

  have cont: continuous_on (λ x, exp(-x) * x^s : ℝ → ℂ) (Icc 0 X),
  { refine continuous_on.mono (cont_integrand $ lt_of_lt_of_le zero_lt_one hs) _,
    simp only [Ici, Icc, set_of_subset_set_of, and_imp],
    intros a ha1 ha2, linarith, },

  have der_ible := (deriv_interval_integrable_A hs hX).add (deriv_interval_integrable_B hs hX),

  have int_eval := integral_eq_sub_of_has_deriv_at_of_le hX cont F_der_I der_ible,
  apply_fun (λ x:ℂ, -x) at int_eval,

  rw [interval_integral.integral_add (deriv_interval_integrable_A hs hX)
  (deriv_interval_integrable_B hs hX), interval_integral.integral_neg, neg_add, neg_neg] at int_eval,
  replace int_eval := eq_sub_of_add_eq int_eval,
  rw [int_eval, sub_neg_eq_add, neg_sub, add_comm, add_sub],
  simp only [sub_left_inj, add_left_inj],
  have: (λ x:ℝ, ↑(exp (-x)) * (s * ↑x ^ (s - 1))) = (λ x:ℝ, s * ↑(exp (-x)) * ↑x ^ (s - 1)),
  { ext1, ring,},
  rw this,
  have t := integral_const_mul s (λ x:ℝ, exp(-x) * x^(s-1)),
  swap, exact 0, swap, exact X, swap, exact measure_space.volume,
  dsimp at t, rw [←t, complex.of_real_zero, complex.zero_cpow],
  { rw [mul_zero, add_zero], congr', ext1, ring },
  { contrapose! hs, rw [hs,complex.zero_re], exact zero_lt_one,}
end

lemma tendsto_partial_gamma {s : ℂ} (hs: 1 ≤ s.re) :
  tendsto (λ Y:ℝ, partial_gamma s Y) at_top (𝓝 $ gamma_complex_integral s) :=
begin
  refine interval_integral_tendsto_integral_Ioi 0 _ tendsto_id,
  split,
  { refine continuous_on.ae_measurable _ measurable_set_Ioi,
    apply (complex.continuous_of_real.comp continuous_neg.exp).continuous_on.mul,
    apply continuous_at.continuous_on,
    intros x hx,
    refine (_: continuous_at (λ x:ℂ, x ^ (s - 1)) ↑x).comp complex.continuous_of_real.continuous_at,
    apply continuous_at_cpow_const, rw complex.of_real_re, exact or.inl hx, },
  rw ←has_finite_integral_norm_iff,
  apply has_finite_integral.congr (gamma_real_integral_convergent hs).2,
  rw eventually_eq,
  refine (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ (λ x hx, _)),
  rw [complex.norm_eq_abs, complex.abs_mul, complex.abs_of_nonneg (real.exp_pos (-x)).le],
  congr, rw (abs_cpow_of_pos_real (s - 1) hx), simp,
end

theorem gamma_integral_recurrence {s : ℂ} (hs: 1 ≤ s.re) :
  gamma_complex_integral (s+1) = s * gamma_complex_integral s :=
begin
  have t1: tendsto (partial_gamma (s+1)) at_top (𝓝 (gamma_complex_integral (s+1))),
  { apply tendsto_partial_gamma, rw [complex.add_re, complex.one_re], linarith, },

  suffices t2: tendsto (partial_gamma (s+1)) at_top (𝓝 $ s * gamma_complex_integral s),
  { apply tendsto_nhds_unique t1 t2 },

  have a: eventually_eq at_top (partial_gamma (s+1)) (λ X:ℝ, s * partial_gamma s X - X^s * exp(-X)),
  { apply eventually_eq_of_mem (Ici_mem_at_top (0:ℝ)),
    intros X hX,
    rw partial_gamma_recurrence hs (mem_Ici.mp hX),
    ring_nf },
  refine tendsto.congr' a.symm _,

  suffices l1: tendsto (λ X:ℝ, -↑X ^ s * exp(-X): ℝ → ℂ) at_top (𝓝 0),
  { simpa using tendsto.add (tendsto.const_mul s (tendsto_partial_gamma hs)) l1 },

  have l2: tendsto (λ X:ℝ, ↑X ^ s * exp(-X) : ℝ → ℂ) at_top (𝓝 0),
  { rw tendsto_zero_iff_norm_tendsto_zero,
    have: eventually_eq at_top (λ (e : ℝ), ∥(e:ℂ) ^ s * ↑(exp (-e))∥ )
      (λ (e : ℝ), e ^ s.re * exp (-e)),
    { refine eventually_eq_of_mem (Ioi_mem_at_top 0) _,
      intros x hx, dsimp,
      rw [complex.abs_mul, abs_cpow_of_pos_real s hx, complex.abs_of_nonneg (exp_pos(-x)).le], },
    rw (tendsto_congr' this),
    simpa using (tendsto_rpow_mul_exp_neg_mul_at_top_nhds_0 s.re (1:ℝ) zero_lt_one), },

  have: (λ X, -↑X ^ s * exp (-X): ℝ → ℂ) = (λ X, (-1) * (↑X ^ s * exp (-X)): ℝ → ℂ) :=
    by ring_nf, rw this,
  have : (0:ℂ) = (-1) * 0 := by ring, rw this,
  exact tendsto.const_mul (-1) l2
end

end gamma_integral_recurrence


/- Now we define `Γ(s)` on the whole complex plane, by recursion. -/

section gamma_def

/- This function is `Γ(s)` if `1-n ≤ s.re`, and junk otherwise .-/
noncomputable def gamma_aux : ℕ → (ℂ → ℂ)
| 0      := gamma_complex_integral
| (n+1)  := λ s:ℂ, (gamma_aux n (s+1)) / s

lemma gamma_aux_recurrence1 (s : ℂ) (n : ℕ) (h1 : 1 - s.re ≤ ↑n ) : gamma_aux n s =
  (gamma_aux n (s+1) ) / s :=
begin
  revert s,
  induction n with n hn,
  { intros s h1, simp only [nat.cast_zero, sub_nonpos] at h1,
    dsimp only [gamma_aux], rw gamma_integral_recurrence h1,
    rw [mul_comm, mul_div_cancel], contrapose! h1, rw h1,
    simp },
  { dsimp only [gamma_aux],
    intros s h1,
    have hh1 : 1 - (s+1).re ≤ n,
    { rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one] at h1,
      rw [complex.add_re, complex.one_re], linarith, },
    rw ←(hn (s+1) hh1) }
end

lemma gamma_aux_recurrence2 (s : ℂ) (n : ℕ) (h1 : 1 - s.re ≤ ↑n) :
  gamma_aux n s = gamma_aux (n+1) s :=
begin
  cases n,
  { simp only [nat.cast_zero, sub_nonpos] at h1,
    dsimp only [gamma_aux], rw gamma_integral_recurrence h1,
    have : s ≠ 0 := by { contrapose! h1, rw h1, simp, },
    field_simp, ring },
  { dsimp only [gamma_aux],
    have : (gamma_aux n (s + 1 + 1)) / (s+1) = gamma_aux n (s + 1),
    { have hh1 : 1 - (s+1).re ≤ n,
      { rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one] at h1,
        rw [complex.add_re, complex.one_re], linarith, },
      rw gamma_aux_recurrence1 (s+1) n hh1, },
    rw this },
end

/-- The `Γ` function (of a complex variable `s`). -/
def gamma (s : ℂ) : ℂ := gamma_aux ⌈ 1 - s.re ⌉₊ s

lemma gamma_eq_gamma_aux (s : ℂ) (n : ℕ) (h1 : 1 - s.re ≤ ↑n) : gamma s = gamma_aux n s :=
begin
  have u : ∀ (k : ℕ), gamma_aux (⌈ 1 - s.re ⌉₊ + k) s = gamma s,
  { intro k, induction k with k hk,
    { dsimp only [gamma], simp, },
    { rw [←hk, nat.succ_eq_add_one, ←add_assoc],
      refine (gamma_aux_recurrence2 s (⌈ 1 - s.re ⌉₊ + k) _).symm,
      rw nat.cast_add,
      have i1 := nat.le_ceil (1 - s.re),
      refine le_add_of_le_of_nonneg i1 _,
      rw [←nat.cast_zero, nat.cast_le], exact nat.zero_le k, } },
  rw [←nat.add_sub_of_le (nat.ceil_le.mpr h1), u (n - ⌈ 1 - s.re ⌉₊)],
end

theorem gamma_recurrence (s : ℂ) (h2 : s ≠ 0) : s * gamma(s) = gamma (s+1) :=
begin
  let n := ⌈ 1 - s.re ⌉₊,
  have t1 : 1 - s.re ≤ n := nat.le_ceil (1 - s.re),
  have t2 : 1 - (s+1).re ≤ n := by { rw [complex.add_re, complex.one_re], linarith, },
  rw [gamma_eq_gamma_aux s n t1, gamma_eq_gamma_aux (s+1) n t2, gamma_aux_recurrence1 s n t1],
  field_simp, ring
end

theorem gamma_eq_integral (s : ℂ) (hs : 1 ≤ s.re) : gamma s = gamma_complex_integral s :=
begin
  refine gamma_eq_gamma_aux s 0 (_ : _ ≤ 0), linarith
end

theorem gamma_integer_eq_factorial (n : ℕ) : gamma (n+1) = nat.factorial n :=
begin
  induction n with n hn,
  { rw [nat.cast_zero, zero_add], rw gamma_eq_integral,
    simpa using gamma_complex_integral_one, simp,},
  rw ←(gamma_recurrence n.succ $ nat.cast_ne_zero.mpr $ nat.succ_ne_zero n),
  { simp only [nat.cast_succ, nat.factorial_succ, nat.cast_mul], congr, exact hn },
end

end gamma_def

section gamma_has_deriv

def integrand (s : ℂ) (x : ℝ) : ℂ := exp(-x) * x^(s-1)
def integrand_real (s x : ℝ) : ℝ := exp(-x) * x^(s-1)
def dgamma_integrand (s : ℂ) (x : ℝ) : ℂ := exp(-x) * log x * x^(s-1)
def dgamma_integrand_real (s x : ℝ) : ℝ := | exp(-x) * log x * x^(s-1) |

lemma dgamma_integrand_is_O_at_top (s : ℝ) : asymptotics.is_O (λ x:ℝ, exp(-x) * log x * x^(s-1))
  (λ x:ℝ, exp(-(1/2) * x) ) at_top :=
begin
  apply asymptotics.is_o.is_O,
  apply asymptotics.is_o_of_tendsto,
  { intros x hx, exfalso, exact  (-(1/2) * x).exp_pos.ne' hx, },
  have : eventually_eq at_top (λ (x : ℝ), exp (-x) * log x * x ^ (s - 1) / exp (-(1 / 2) * x))
    (λ (x : ℝ),  (λ z:ℝ, exp (1 / 2 * z) / z ^ s) x * (λ z:ℝ, z / log z) x)⁻¹,
  { apply eventually_of_mem, exact Ioi_mem_at_top 1, intros x hx, dsimp,
    rw mem_Ioi at hx,
    rw [exp_neg, neg_mul, exp_neg, rpow_sub (lt_trans zero_lt_one hx)],
    have : exp x = exp(x/2) * exp(x/2) := by { rw ←real.exp_add, simp, }, rw this,
    field_simp [(lt_trans zero_lt_one hx).ne', exp_ne_zero (x/2)], ring, },
  apply tendsto.congr' this.symm,
  apply tendsto.inv_tendsto_at_top,
  apply tendsto.at_top_mul_at_top (tendsto_exp_mul_div_rpow_at_top s (1/2) one_half_pos),
  refine tendsto.congr' _ (tendsto.comp (tendsto_exp_div_pow_at_top 1) tendsto_log_at_top),
  apply eventually_eq_of_mem (Ioi_mem_at_top (0:ℝ)),
  intros x hx, simp [exp_log hx],
end

/-- Bound for `x log x` in the interval `(0, 1]`. -/
lemma log_bound (x: ℝ) (hx : 0 < x ∧ x ≤ 1) : | log x * x | < 1 :=
begin
  have : 0 < 1/x := by simpa only [one_div, inv_pos] using hx.1,
  replace := log_le_sub_one_of_pos this,
  replace : log (1 / x) < 1/x := by linarith,
  rw [log_div one_ne_zero hx.1.ne', log_one, zero_sub, lt_div_iff hx.1] at this,
  have aux : 0 ≤ -log x * x,
  { refine mul_nonneg _ hx.1.le, rw ←log_inv, apply log_nonneg,
    rw [←(le_inv hx.1 zero_lt_one), inv_one], exact hx.2, },
  rw [←(abs_of_nonneg aux), neg_mul, abs_neg] at this, exact this,
end

/-- Bound for `x^t log x` in the interval `(0, 1]`, for positive real `t`. -/
lemma log_rpow_bound (x t : ℝ) (hx : 0 < x ∧ x ≤ 1) (ht : 0 < t) : | log x * x ^ t | < 1 / t :=
begin
  rw lt_div_iff ht,
  have := log_bound (x ^ t) ⟨rpow_pos_of_pos hx.1 t, rpow_le_one hx.1.le hx.2 ht.le⟩,
  rw [log_rpow hx.1, mul_assoc, abs_mul, abs_of_pos ht, mul_comm] at this,
  exact this,
end

/-- Absolute convergence of the integral which will give the derivative of the `Γ` function on
`1 < re s`. -/
lemma dgamma_integral_abs_convergent (s : ℝ) (hs : 1 < s) :
  integrable_on (λ x:ℝ, ∥ exp (-x) * log x * x ^ (s-1) ∥ ) (Ioi 0) :=
begin
  have : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := by simp,
  rw [this,integrable_on_union],
  split,
  { split,
    { refine continuous_on.ae_measurable (continuous_on.mul _ _).norm measurable_set_Ioc,
      { apply continuous_on.mul (continuous_exp.comp continuous_neg).continuous_on,
        apply continuous_on.mono continuous_on_log, simp, },
      { apply continuous_at.continuous_on, intros x hx,
        apply continuous_at.rpow continuous_at_id continuous_at_const,
        dsimp, right, linarith, },},
    { apply has_finite_integral_of_bounded,
      swap, { exact 1 / (s - 1), },
      refine (ae_restrict_iff' measurable_set_Ioc).mpr (ae_of_all _ (λ x hx, _)),
      rw [norm_norm, norm_eq_abs, mul_assoc, abs_mul],
      have : 1/(s-1) = 1 * (1 / (s-1)) := by ring, rw this,
      refine mul_le_mul _ _ (by apply abs_nonneg) (zero_le_one),
      { rw [abs_of_pos (exp_pos(-x)), exp_le_one_iff, neg_le, neg_zero], exact hx.1.le },
      { apply le_of_lt, refine log_rpow_bound x (s-1) _ (by linarith),
        rw Ioc at hx, exact hx, }, }, },
  { have := asymptotics.is_O.norm_left (dgamma_integrand_is_O_at_top s),
    refine integrable_of_is_O_exp_neg one_half_pos (continuous_on.mul _ _).norm this,
    { apply continuous_on.mul (continuous_exp.comp continuous_neg).continuous_on,
      apply continuous_on.mono continuous_on_log, simp, },
    { apply continuous_at.continuous_on, intros x hx,
      apply continuous_at.rpow continuous_at_id continuous_at_const,
      dsimp, right, linarith, }, }
end

/-- A uniform bound for the `s`-derivative of the `Γ` integrand for `s` in vertical strips. -/
lemma loc_unif_bound_dgamma_integrand {t : ℂ} {s1 s2 x : ℝ} (ht : s1 ≤ t.re ∧ t.re ≤ s2) (hx: 0 < x)
: ∥ dgamma_integrand t x ∥ ≤ (dgamma_integrand_real s1 x) + (dgamma_integrand_real s2 x) :=
begin
  by_cases (1 ≤ x),
  { suffices: ∥ dgamma_integrand t x ∥ ≤ dgamma_integrand_real s2 x, -- case 1 ≤ x
    { have: 0 ≤ dgamma_integrand_real s1 x := by apply abs_nonneg, linarith, },
    rw [dgamma_integrand, dgamma_integrand_real, complex.norm_eq_abs, complex.abs_mul,
    complex.abs_mul, abs_mul, abs_mul, complex.abs_of_real, complex.abs_of_real],
    refine mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg $ exp $ -x) (abs_nonneg $ log x)),
    rw abs_cpow_of_pos_real (t-1) hx,
    refine le_trans _ (le_abs_self _),
    apply rpow_le_rpow_of_exponent_le h, rw [complex.sub_re, complex.one_re], linarith, },
  { simp only [not_le] at h, -- case x < 1
    suffices: ∥ dgamma_integrand t x ∥ ≤ dgamma_integrand_real s1 x,
    { have : 0 ≤ dgamma_integrand_real s2 x := by apply abs_nonneg, linarith, },
    rw [dgamma_integrand, dgamma_integrand_real, complex.norm_eq_abs, complex.abs_mul,
    complex.abs_mul, abs_mul, abs_mul, complex.abs_of_real, complex.abs_of_real],
    refine mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg $ exp $ -x) (abs_nonneg $ log x)),
    rw abs_cpow_of_pos_real, swap, exact hx,
    refine le_trans _ (le_abs_self _),
    apply rpow_le_rpow_of_exponent_ge hx h.le,rw [complex.sub_re, complex.one_re], linarith, },
end

open complex

/-- The `Γ` function is complex-differentiable at any `s ∈ ℂ` with `1 < re s`. -/
theorem differentiable_at_gamma_integral {s : ℂ} (hs : 1 < s.re) :
  differentiable_at ℂ gamma_complex_integral s :=
begin
  let ε := (s.re - 1) / 2,
  let μ := volume.restrict (Ioi (0:ℝ)),
  let bound := (λ x:ℝ, dgamma_integrand_real (s.re - ε) x + dgamma_integrand_real (s.re + ε) x),

  have eps_pos: 0 < ε := by { refine div_pos _ zero_lt_two, linarith },
  have hF_meas : ∀ᶠ (t : ℂ) in 𝓝 s, ae_measurable (integrand t) μ,
  { apply eventually_of_forall, intro s,
    exact continuous_on.ae_measurable cont_integrand' measurable_set_Ioi, },
  have hF_int : measure_theory.integrable (integrand s) μ := gamma_complex_integral_convergent hs.le,
  have hF'_meas : ae_measurable (dgamma_integrand s) μ,
  { refine continuous_on.ae_measurable _ measurable_set_Ioi,
    have : dgamma_integrand s = (λ x:ℝ, ↑(real.exp(-x)) * (↑x) ^ (s-1) * ↑ (log x) : ℝ → ℂ),
    { ext1, simp only [dgamma_integrand], ring },
    rw this,
    refine continuous_on.mul cont_integrand' _,
    apply continuous_at.continuous_on, intros x hx,
    refine continuous_at.comp continuous_of_real.continuous_at _,
    rw mem_Ioi at hx, exact continuous_at_log hx.ne', },
  have h_bound : ∀ᵐ (x : ℝ) ∂μ, ∀ (t : ℂ), t ∈ metric.ball s ε → ∥dgamma_integrand t x∥ ≤ bound x,
  { refine (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ (λ x hx, _)),
    intros t ht,
    refine loc_unif_bound_dgamma_integrand _ hx,
    rw [metric.mem_ball, complex.dist_eq] at ht,
    replace ht := lt_of_le_of_lt (complex.abs_re_le_abs $ t - s ) ht,
    rw [complex.sub_re, @abs_sub_lt_iff ℝ _ t.re s.re ((s.re - 1) / 2) ] at ht,
    simp only [ε], split, linarith, linarith, },
  have bound_integrable : measure_theory.integrable bound μ,
  { apply integrable.add,
    { refine dgamma_integral_abs_convergent (s.re - ε) _,
      field_simp, rw one_lt_div,
      { linarith }, { exact zero_lt_two }, },
    { refine dgamma_integral_abs_convergent (s.re + ε) _, linarith, }, },
  have h_diff : ∀ᵐ (x : ℝ) ∂μ, ∀ (t : ℂ), t ∈ metric.ball s ε
    → has_deriv_at (λ (u : ℂ), integrand u x) (dgamma_integrand t x) t,
  { refine (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ (λ x hx, _)),
    intros t ht, rw mem_Ioi at hx,
    simp only [integrand, dgamma_integrand],
    rw mul_assoc,
    apply has_deriv_at.const_mul,
    rw [of_real_log hx.le, mul_comm],
    have := has_deriv_at.const_cpow (has_deriv_at.sub_const (has_deriv_at_id t) 1)
      (or.inl (of_real_ne_zero.mpr hx.ne')),
    rwa mul_one at this },
  have diff := has_deriv_at_integral_of_dominated_loc_of_deriv_le eps_pos hF_meas hF_int hF'_meas
    h_bound bound_integrable h_diff,
  exact has_deriv_at.differentiable_at diff.2,
end

lemma differentiable_at_gamma_aux (s : ℂ) (n : ℕ) (h1 : (1 - s.re) < n ) (h2 : ∀ m:ℕ, s + m ≠ 0) :
  differentiable_at ℂ (gamma_aux n) s :=
begin
  revert s,
  induction n with n hn,
  { intros s h1 h2,
    apply differentiable_at_gamma_integral,
    rw nat.cast_zero at h1, linarith },
  { intros s h1 h2,
    dsimp only [gamma_aux],
    specialize hn (s + 1),
    have a : 1 - (s + 1).re < ↑n,
    { rw nat.cast_succ at h1, rw [complex.add_re, complex.one_re], linarith },
    have b: ∀ m:ℕ, s + 1 + m ≠ 0,
    { intro m, have := h2 (1+m), rwa [nat.cast_add, nat.cast_one, ←add_assoc] at this },
    replace hn := hn a b,
    have : s ≠ 0 := by simpa using h2 0,
    refine differentiable_at.div _ differentiable_at_id this,
    refine differentiable_at.comp _ hn _,
    simp }
end

theorem differentiable_at_gamma (s : ℂ) (hs : ∀ m:ℕ, s + m ≠ 0) : differentiable_at ℂ gamma s :=
begin
  let n := ⌊1 - s.re⌋₊ + 1,
  have hn : 1 - s.re < n := nat.lt_floor_add_one (1 - s.re),
  refine differentiable_at.congr_of_eventually_eq (differentiable_at_gamma_aux s n hn hs) _,
  let S := { t : ℂ | 1 - t.re < n },
  have : S ∈ 𝓝 s,
  { rw mem_nhds_iff, use S,
    refine ⟨by refl, _, hn⟩,
    have: S = re⁻¹' (Ioi (1-n : ℝ)),
    { ext, rw [preimage,Ioi, mem_set_of_eq, mem_set_of_eq, mem_set_of_eq], exact sub_lt },
    rw this,
    refine continuous.is_open_preimage continuous_re _ is_open_Ioi, },
  apply eventually_eq_of_mem this,
  intros t ht, rw mem_set_of_eq at ht,
  apply gamma_eq_gamma_aux, exact ht.le,
end

end gamma_has_deriv
