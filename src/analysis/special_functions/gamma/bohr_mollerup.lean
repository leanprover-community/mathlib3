/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import analysis.special_functions.gamma.basic

/-! # Convexity properties of the Gamma function

In this file, we prove that `Gamma` and `log ∘ Gamma` are convex functions on the positive real
line. We then prove the Bohr-Mollerup theorem, which characterises `Gamma` as the *unique*
positive-real-valued, log-convex function on the positive reals satisfying `f (x + 1) = x f x` and
`f 1 = 1`.

The proof of the Bohr-Mollerup theorem is bound up with the proof of (a weak form of) the Euler
limit formula, `real.bohr_mollerup.tendsto_log_gamma_seq`, stating that for positive
real `x` the sequence `x * log n + log n! - ∑ (m : ℕ) in finset.range (n + 1), log (x + m)`
tends to `log Γ(x)` as `n → ∞`. We prove that any function satisfying the hypotheses of the
Bohr-Mollerup theorem must agree with the limit in the Euler limit formula, so there is at most one
such function; then we show that `Γ` satisfies these conditions.

Since most of the auxiliary lemmas for the Bohr-Mollerup theorem are of no relevance outside the
context of this proof, we place them in a separate namespace `real.bohr_mollerup` to avoid clutter.
(This includes the logarithmic form of the Euler limit formula, since later we will prove a more
general form of the Euler limit formula valid for any real or complex `x`; see
`real.Gamma_seq_tendsto_Gamma` and `complex.Gamma_seq_tendsto_Gamma` in the file
`analysis.special_functions.gamma.beta`.)
-/

noncomputable theory
open filter set measure_theory
open_locale nat ennreal topology big_operators

namespace real

section convexity

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

end convexity

section bohr_mollerup

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
