/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import measure_theory.integral.exp_decay

/-!
# The Gamma function

This file defines the `Γ` function (of a real or complex variable `s`). We define this by Euler's
integral `Γ(s) = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1)` in a range where we can prove this is
convergent: presently `1 ≤ s` in the real case, and `1 ≤ re s` in the complex case (which is
non-optimal, but the optimal bound of `0 < s`, resp `0 < re s`, is harder to prove using the
methods in the library).

We show that this integral satisfies `Γ(1) = 1` and `Γ(s + 1) = s * Γ(s)`; hence we can define
`Γ(s)` for all `s` as the unique function satisfying this recurrence and agreeing with Euler's
integral in the convergence range.

TODO: Holomorpy in `s` (away from the poles at `-n : n ∈ ℕ`) will be added in a future PR.

## Tags

Gamma
-/

noncomputable theory
open filter interval_integral set real measure_theory
open_locale topological_space

lemma integral_exp_neg_Ioi : ∫ (x : ℝ) in Ioi 0, exp (-x) = 1 :=
begin
  refine tendsto_nhds_unique (interval_integral_tendsto_integral_Ioi _ _ tendsto_id) _,
  { simpa only [neg_mul, one_mul] using exp_neg_integrable_on_Ioi 0 zero_lt_one, },
  { simpa using tendsto_exp_neg_at_top_nhds_0.const_sub 1, },
end

namespace real

/-- Asymptotic bound for the Γ function integrand. -/
lemma Gamma_integrand_is_O (s : ℝ) : asymptotics.is_O (λ x:ℝ, exp (-x) * x ^ s)
  (λ x:ℝ, exp (-(1/2) * x)) at_top :=
begin
  refine asymptotics.is_o.is_O (asymptotics.is_o_of_tendsto _ _),
  { intros x hx, exfalso, exact (exp_pos (-(1 / 2) * x)).ne' hx },
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

See `Gamma_integral_convergent` for a proof of the convergence of the integral for `1 ≤ s`. -/
def Gamma_integral (s : ℝ) : ℝ := ∫ x in Ioi (0:ℝ), exp (-x) * x ^ (s - 1)

/-- The integral defining the Γ function converges for real `s` with `1 ≤ s`.

This is not optimal, but the optimal bound (convergence for `0 < s`) is hard to establish with the
results currently in the library. -/
lemma Gamma_integral_convergent {s : ℝ} (h : 1 ≤ s) :
  integrable_on (λ x:ℝ, exp (-x) * x ^ (s - 1)) (Ioi 0) :=
begin
  refine integrable_of_is_O_exp_neg one_half_pos _ (Gamma_integrand_is_O _ ),
  refine continuous_on_id.neg.exp.mul (continuous_on_id.rpow_const _),
  intros x hx, right, simpa only [sub_nonneg] using h,
end

lemma Gamma_integral_one : Gamma_integral 1 = 1 :=
by simpa only [Gamma_integral, sub_self, rpow_zero, mul_one] using integral_exp_neg_Ioi

end real

namespace complex
/- Technical note: In defining the Gamma integrand exp (-x) * x ^ (s - 1) for s complex, we have to
make a choice between ↑(real.exp (-x)), complex.exp (↑(-x)), and complex.exp (-↑x), all of which are
equal but not definitionally so. We use the first of these throughout. -/


/-- The integral defining the Γ function converges for complex `s` with `1 ≤ re s`.

This is proved by reduction to the real case. The bound is not optimal, but the optimal bound
(convergence for `0 < re s`) is hard to establish with the results currently in the library. -/
lemma Gamma_integral_convergent {s : ℂ} (hs : 1 ≤ s.re) :
  integrable_on (λ x, (-x).exp * x ^ (s - 1) : ℝ → ℂ) (Ioi 0) :=
begin
  -- This is slightly subtle if `s` is non-real but `s.re = 1`, as the integrand is not continuous
  -- at the lower endpoint. However, it is continuous on the interior, and its norm is continuous
  -- at the endpoint, which is good enough.
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
    simp }
end

/-- Euler's integral for the `Γ` function (of a complex variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `complex.Gamma_integral_convergent` for a proof of the convergence of the integral for
`1 ≤ re s`. -/
def Gamma_integral (s : ℂ) : ℂ := ∫ x in Ioi (0:ℝ), ↑(-x).exp * ↑x ^ (s - 1)

lemma Gamma_integral_of_real (s : ℝ) :
  Gamma_integral ↑s = ↑(s.Gamma_integral) :=
begin
  rw [real.Gamma_integral, ←integral_of_real],
  refine set_integral_congr measurable_set_Ioi _,
  intros x hx, dsimp only,
  rw [of_real_mul, of_real_cpow (mem_Ioi.mp hx).le],
  simp,
end

lemma Gamma_integral_one : Gamma_integral 1 = 1 :=
begin
  rw [←of_real_one, Gamma_integral_of_real, of_real_inj],
  exact real.Gamma_integral_one,
end

end complex

/- Now we establish the recurrence relation `Γ(s + 1) = s * Γ(s)` using integration by parts. -/

namespace complex

section Gamma_recurrence

/- first some lemmas about real and complex functions -/

/- This is not a special case of `continuous_at_cpow_const`, since here we get continuity on a
larger domain (including 0) at the cost of stronger hypotheses on the exponent. -/
lemma cts_cpow {s : ℂ} (hs : 0 < s.re): continuous_on (λ x, x ^ s : ℝ → ℂ) (Ici 0) :=
begin
  -- There must be a better way of doing this.
  intros x hx,
  by_cases 0 < x,
  { apply continuous_at.continuous_within_at,
    refine (_ : continuous_at (λ x : ℂ, x ^ s) ↑x).comp continuous_of_real.continuous_at,
    apply continuous_at_cpow_const, rw of_real_re, exact or.inl h },
  have : x = 0 := by { rw mem_Ici at hx, linarith }, rw this,
  have hs2 : s ≠ 0 := by { contrapose! hs, rw [hs, zero_re], },
  rw continuous_within_at,
  have : ↑(0 : ℝ) ^ s = (0 : ℂ) := by { rw of_real_zero, exact zero_cpow hs2 },
  rw [this, tendsto_zero_iff_norm_tendsto_zero],
  have u: eq_on (λ (e : ℝ), e ^ s.re)  (λ (e : ℝ), abs(↑e ^ s)) (Ici 0),
  { intros y hy, exact (abs_cpow_eq_rpow_re_of_nonneg hy hs.ne').symm },
  have w: tendsto (λ (e : ℝ), e ^ s.re) (𝓝[Ici 0] 0) (𝓝 (0 ^ s.re)),
  { exact tendsto.rpow_const continuous_within_at_id (or.inr hs.le), },
  rw zero_rpow hs.ne' at w,
  exact tendsto.congr' (eventually_nhds_within_of_forall u) w,
end

lemma has_deriv_at_coe (t : ℝ) : has_deriv_at (coe : ℝ → ℂ) 1 t :=
begin
  rw has_deriv_at_iff_tendsto,
  simpa using tendsto_const_nhds,
end

lemma has_deriv_at_of_real {f : ℝ → ℝ} {d x : ℝ} (hf : has_deriv_at f d x) :
  (has_deriv_at ((coe ∘ f) : ℝ → ℂ) ↑d x) :=
by simpa using has_deriv_at.scomp x (has_deriv_at_coe $ f x) hf

/-- The indefinite version of the Γ function, Γ(s, X) = ∫ x ∈ 0..X, exp(-x) x ^ (s - 1). -/
def partial_Gamma (s : ℂ) (X : ℝ) : ℂ := ∫ x in 0..X, (-x).exp * x ^ (s - 1)

lemma tendsto_partial_Gamma {s : ℂ} (hs: 1 ≤ s.re) :
  tendsto (λ X:ℝ, partial_Gamma s X) at_top (𝓝 $ Gamma_integral s) :=
interval_integral_tendsto_integral_Ioi 0 (Gamma_integral_convergent hs) tendsto_id

lemma Gamma_integrand_interval_integrable (s : ℂ) {X : ℝ} (hs : 1 ≤ s.re) (hX : 0 ≤ X):
  interval_integrable (λ x, (-x).exp * x ^ (s - 1) : ℝ → ℂ) volume 0 X :=
begin
  rw interval_integrable_iff_integrable_Ioc_of_le hX,
  exact integrable_on.mono_set (Gamma_integral_convergent hs) Ioc_subset_Ioi_self
end

lemma Gamma_integrand_deriv_integrable_A {s : ℂ} (hs: 1 ≤ s.re) {X : ℝ} (hX : 0 ≤ X):
 interval_integrable (λ x, -((-x).exp * x ^ s) : ℝ → ℂ) volume 0 X :=
begin
  have t := (Gamma_integrand_interval_integrable (s+1) _ hX).neg,
  { simpa using t },
  { simp only [add_re, one_re], linarith,},
end

lemma Gamma_integrand_deriv_integrable_B {s : ℂ} (hs: 1 ≤ s.re) {Y : ℝ} (hY : 0 ≤ Y) :
  interval_integrable (λ (x : ℝ), (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) volume 0 Y :=
begin
  have: (λ x, (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) =
    (λ x, s * ((-x).exp * x ^ (s - 1)) : ℝ → ℂ) := by { ext1, ring, },
  rw [this, interval_integrable_iff_integrable_Ioc_of_le hY],
  split,
  { refine (continuous_on_const.mul _).ae_strongly_measurable measurable_set_Ioc,
    apply (continuous_of_real.comp continuous_neg.exp).continuous_on.mul,
    apply continuous_at.continuous_on,
    intros x hx,
    refine (_ : continuous_at (λ x:ℂ, x ^ (s - 1)) _).comp continuous_of_real.continuous_at,
    apply continuous_at_cpow_const, rw of_real_re, exact or.inl hx.1, },
  apply has_finite_integral_of_bounded, swap, exact s.abs * Y ^ (s.re - 1),
  refine (ae_restrict_iff' measurable_set_Ioc).mpr (ae_of_all _ (λ x hx, _)),
  rw [norm_eq_abs, abs_mul,abs_mul, abs_of_nonneg (exp_pos(-x)).le],
  refine mul_le_mul_of_nonneg_left _ (abs_nonneg s),
  have i1: (-x).exp ≤ 1 := by { simpa using hx.1.le, },
  have i2: abs (↑x ^ (s - 1)) ≤ Y ^ (s.re - 1),
  { rw [abs_cpow_eq_rpow_re_of_pos hx.1 _, sub_re, one_re],
    apply rpow_le_rpow hx.1.le hx.2, linarith, },
  simpa using mul_le_mul i1 i2 (abs_nonneg (↑x ^ (s - 1))) zero_le_one,
end

lemma partial_Gamma_recurrence {s : ℂ} (hs: 1 ≤ s.re) {X : ℝ} (hX : 0 ≤ X) :
  partial_Gamma (s + 1) X = s * partial_Gamma s X - (-X).exp * X ^ s :=
begin
  rw [partial_Gamma, partial_Gamma, add_sub_cancel],
  have F_der_I: (∀ (x:ℝ), (x ∈ Ioo 0 X) → has_deriv_at (λ x, (-x).exp * x ^ s : ℝ → ℂ)
    ( -((-x).exp * x ^ s) + (-x).exp * (s * x ^ (s - 1))) x),
  { intros x hx,
    have d1 : has_deriv_at (λ (y: ℝ), (-y).exp) (-(-x).exp) x,
    { simpa using (has_deriv_at_neg x).exp },
    have d2: has_deriv_at (λ (y : ℝ), ↑y ^ s) (s * x ^ (s - 1)) x,
    { have t := @has_deriv_at.cpow_const _ _ _ s (has_deriv_at_id ↑x),
      simp only [id.def, of_real_re, of_real_im,
        ne.def, eq_self_iff_true, not_true, or_false, mul_one] at t,
      simpa using has_deriv_at.comp _ (t hx.left) (has_deriv_at_coe x), },
    simpa using has_deriv_at.mul (has_deriv_at_of_real d1) d2 },
  have cont := (continuous_of_real.comp continuous_neg.exp).continuous_on.mul
    (cts_cpow (lt_of_lt_of_le zero_lt_one hs)),
  have der_ible := (Gamma_integrand_deriv_integrable_A hs hX).add
    (Gamma_integrand_deriv_integrable_B hs hX),
  have int_eval := integral_eq_sub_of_has_deriv_at_of_le hX (cont.mono Icc_subset_Ici_self)
    F_der_I der_ible,
  -- We are basically done here but manipulating the output into the right form is fiddly.
  apply_fun (λ x:ℂ, -x) at int_eval,
  rw [interval_integral.integral_add (Gamma_integrand_deriv_integrable_A hs hX)
    (Gamma_integrand_deriv_integrable_B hs hX), interval_integral.integral_neg, neg_add, neg_neg]
    at int_eval,
  replace int_eval := eq_sub_of_add_eq int_eval,
  rw [int_eval, sub_neg_eq_add, neg_sub, add_comm, add_sub],
  simp only [sub_left_inj, add_left_inj],
  have : (λ x, (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) = (λ x, s * (-x).exp * x ^ (s - 1) : ℝ → ℂ),
  { ext1, ring,},
  rw this,
  have t := @integral_const_mul (0:ℝ) X volume _ _ s (λ x:ℝ, (-x).exp * x ^ (s - 1)),
  dsimp at t, rw [←t, of_real_zero, zero_cpow],
  { rw [mul_zero, add_zero], congr', ext1, ring },
  { contrapose! hs, rw [hs, zero_re], exact zero_lt_one,}
end

theorem Gamma_integral_recurrence {s : ℂ} (hs: 1 ≤ s.re) :
  Gamma_integral (s + 1) = s * Gamma_integral s :=
begin
  have t1: tendsto (partial_Gamma (s+1)) at_top (𝓝 (Gamma_integral (s+1))),
  { apply tendsto_partial_Gamma, rw [add_re, one_re], linarith, },
  suffices t2: tendsto (partial_Gamma (s+1)) at_top (𝓝 $ s * Gamma_integral s),
  { apply tendsto_nhds_unique t1 t2 },
  have a: eventually_eq at_top
    (partial_Gamma (s+1)) (λ X:ℝ, s * partial_Gamma s X - X ^ s * (-X).exp),
  { apply eventually_eq_of_mem (Ici_mem_at_top (0:ℝ)),
    intros X hX,
    rw partial_Gamma_recurrence hs (mem_Ici.mp hX),
    ring_nf, },
  refine tendsto.congr' a.symm _,
  suffices l1: tendsto (λ X:ℝ, -(↑X ^ s) * (-X).exp : ℝ → ℂ) at_top (𝓝 0),
  { simpa using tendsto.add (tendsto.const_mul s (tendsto_partial_Gamma hs)) l1 },
  have l2: tendsto (λ X:ℝ, ↑X ^ s * (-X).exp : ℝ → ℂ) at_top (𝓝 0),
  { rw tendsto_zero_iff_norm_tendsto_zero,
    have: eventually_eq at_top (λ (e : ℝ), ∥(e:ℂ) ^ s * ↑((-e).exp)∥ )
      (λ (e : ℝ), e ^ s.re * (-e).exp ),
    { refine eventually_eq_of_mem (Ioi_mem_at_top 0) _,
      intros x hx, dsimp,
      rw [abs_mul, abs_cpow_eq_rpow_re_of_pos hx, abs_of_nonneg (exp_pos(-x)).le], },
    rw (tendsto_congr' this),
    simpa using (tendsto_rpow_mul_exp_neg_mul_at_top_nhds_0 s.re (1:ℝ) zero_lt_one), },
  have: (λ X, -↑X ^ s *  (-X).exp : ℝ → ℂ) = (λ X, (-1) * (↑X ^ s *  (-X).exp ): ℝ → ℂ) :=
    by ring_nf, rw this,
  have : (0:ℂ) = (-1) * 0 := by ring, rw this,
  exact tendsto.const_mul (-1) l2,
end

end Gamma_recurrence

/- Now we define `Γ(s)` on the whole complex plane, by recursion. -/

section Gamma_def

/-- This function is `Γ(s)` if `1-n ≤ s.re`, and junk otherwise. -/
noncomputable def Gamma_aux : ℕ → (ℂ → ℂ)
| 0      := Gamma_integral
| (n+1)  := λ s:ℂ, (Gamma_aux n (s+1)) / s

lemma Gamma_aux_recurrence1 (s : ℂ) (n : ℕ) (h1 : 1 - s.re ≤ ↑n ) : Gamma_aux n s =
  (Gamma_aux n (s+1) ) / s :=
begin
  revert s,
  induction n with n hn,
  { intros s h1, simp only [nat.cast_zero, sub_nonpos] at h1,
    dsimp only [Gamma_aux], rw Gamma_integral_recurrence h1,
    rw [mul_comm, mul_div_cancel], contrapose! h1, rw h1,
    simp },
  { dsimp only [Gamma_aux],
    intros s h1,
    have hh1 : 1 - (s+1).re ≤ n,
    { rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one] at h1,
      rw [add_re, one_re], linarith, },
    rw ←(hn (s+1) hh1) }
end

lemma Gamma_aux_recurrence2 (s : ℂ) (n : ℕ) (h1 : 1 - s.re ≤ ↑n) :
  Gamma_aux n s = Gamma_aux (n+1) s :=
begin
  cases n,
  { simp only [nat.cast_zero, sub_nonpos] at h1,
    dsimp only [Gamma_aux], rw Gamma_integral_recurrence h1,
    have : s ≠ 0 := by { contrapose! h1, rw h1, simp, },
    field_simp, ring },
  { dsimp only [Gamma_aux],
    have : (Gamma_aux n (s + 1 + 1)) / (s+1) = Gamma_aux n (s + 1),
    { have hh1 : 1 - (s+1).re ≤ n,
      { rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one] at h1,
        rw [add_re, one_re], linarith, },
      rw Gamma_aux_recurrence1 (s+1) n hh1, },
    rw this },
end

/-- The `Γ` function (of a complex variable `s`). -/
def Gamma (s : ℂ) : ℂ := Gamma_aux ⌈ 1 - s.re ⌉₊ s

lemma Gamma_eq_Gamma_aux (s : ℂ) (n : ℕ) (h1 : 1 - s.re ≤ ↑n) : Gamma s = Gamma_aux n s :=
begin
  have u : ∀ (k : ℕ), Gamma_aux (⌈ 1 - s.re ⌉₊ + k) s = Gamma s,
  { intro k, induction k with k hk,
    { simp [Gamma],},
    { rw [←hk, nat.succ_eq_add_one, ←add_assoc],
      refine (Gamma_aux_recurrence2 s (⌈ 1 - s.re ⌉₊ + k) _).symm,
      rw nat.cast_add,
      have i1 := nat.le_ceil (1 - s.re),
      refine le_add_of_le_of_nonneg i1 _,
      rw [←nat.cast_zero, nat.cast_le], exact nat.zero_le k, } },
  rw [←nat.add_sub_of_le (nat.ceil_le.mpr h1), u (n - ⌈ 1 - s.re ⌉₊)],
end

theorem Gamma_recurrence (s : ℂ) (h2 : s ≠ 0) : s * Gamma(s) = Gamma (s+1) :=
begin
  let n := ⌈ 1 - s.re ⌉₊,
  have t1 : 1 - s.re ≤ n := nat.le_ceil (1 - s.re),
  have t2 : 1 - (s+1).re ≤ n := by { rw [add_re, one_re], linarith, },
  rw [Gamma_eq_Gamma_aux s n t1, Gamma_eq_Gamma_aux (s+1) n t2, Gamma_aux_recurrence1 s n t1],
  field_simp, ring
end

theorem Gamma_eq_integral (s : ℂ) (hs : 1 ≤ s.re) : Gamma s = Gamma_integral s :=
begin
  refine Gamma_eq_Gamma_aux s 0 (_ : _ ≤ 0), linarith
end

theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n+1) = nat.factorial n :=
begin
  induction n with n hn,
  { rw [nat.cast_zero, zero_add], rw Gamma_eq_integral,
    simpa using Gamma_integral_one, simp,},
  rw ←(Gamma_recurrence n.succ $ nat.cast_ne_zero.mpr $ nat.succ_ne_zero n),
  { simp only [nat.cast_succ, nat.factorial_succ, nat.cast_mul], congr, exact hn },
end

end Gamma_def

end complex
