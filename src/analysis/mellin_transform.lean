/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import analysis.special_functions.improper_integrals
import analysis.calculus.parametric_integral

/-! # The Mellin transform

We define the Mellin transform of a locally integrable function on `Ioi 0`, and show it is
differentiable in a suitable vertical strip.

## Main statements

- `mellin` : the Mellin transform `∫ (t : ℝ) in Ioi 0, t ^ (s - 1) • f t`,
  where `s` is a complex number.
- `mellin_differentiable_at_of_is_O_rpow` : if `f` is `O(x ^ (-a))` at infinity, and
  `O(x ^ (-b))` at 0, then `mellin f` is holomorphic on the domain `b < re s < a`.

-/

open measure_theory set filter asymptotics topological_space

open_locale topology

noncomputable theory

section defs

variables {E : Type*} [normed_add_comm_group E]

/-- The Mellin transform of a function `f` (for a complex exponent `s`), defined as the integral of
`t ^ (s - 1) • f` over `Ioi 0`. -/
def mellin [normed_space ℂ E] [complete_space E] (f : ℝ → E) (s : ℂ) : E :=
∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) • f t

end defs

open real complex (hiding exp abs_of_nonneg)

variables {E : Type*} [normed_add_comm_group E]

section mellin_convergent
/-! ## Convergence of Mellin transform integrals -/

/-- Auxiliary lemma to reduce convergence statements from vector-valued functions to real
scalar-valued functions. -/
lemma mellin_convergent_iff_norm [normed_space ℂ E] {f : ℝ → E}
  {T : set ℝ} (hT : T ⊆ Ioi 0) (hT' : measurable_set T)
  (hfc : ae_strongly_measurable f $ volume.restrict $ Ioi 0) {s : ℂ} :
  integrable_on (λ t : ℝ, (t : ℂ) ^ (s - 1) • f t) T
  ↔ integrable_on (λ t : ℝ, t ^ (s.re - 1) * ‖f t‖) T :=
begin
  have : ae_strongly_measurable (λ t : ℝ, (t : ℂ) ^ (s - 1) • f t) (volume.restrict T),
  { refine ((continuous_at.continuous_on _).ae_strongly_measurable hT').smul (hfc.mono_set hT),
    exact λ t ht, continuous_at_of_real_cpow_const _ _ (or.inr $ ne_of_gt (hT ht)) },
  rw [integrable_on, ←integrable_norm_iff this, ←integrable_on],
  refine integrable_on_congr_fun (λ t ht, _) hT',
  simp_rw [norm_smul, complex.norm_eq_abs, abs_cpow_eq_rpow_re_of_pos (hT ht), sub_re, one_re],
end

/-- If `f` is a locally integrable real-valued function which is `O(x ^ (-a))` at `∞`, then for any
`s < a`, its Mellin transform converges on some neighbourhood of `+∞`. -/
lemma mellin_convergent_top_of_is_O
  {f : ℝ → ℝ} (hfc : ae_strongly_measurable f $ volume.restrict (Ioi 0))
  {a s : ℝ} (hf : is_O at_top f (λ t, t ^ (-a))) (hs : s < a) :
  ∃ (c : ℝ), 0 < c ∧ integrable_on (λ t : ℝ, t ^ (s - 1) * f t) (Ioi c) :=
begin
  obtain ⟨d, hd, hd'⟩ := hf.exists_pos,
  simp_rw [is_O_with, eventually_at_top] at hd',
  obtain ⟨e, he⟩ := hd',
  have he' : 0 < max e 1, from zero_lt_one.trans_le (le_max_right _ _),
  refine ⟨max e 1, he', _, _⟩,
  { refine ae_strongly_measurable.mul _ (hfc.mono_set (Ioi_subset_Ioi he'.le)),
    refine (continuous_at.continuous_on (λ t ht, _)).ae_strongly_measurable measurable_set_Ioi,
    exact continuous_at_rpow_const _ _ (or.inl $ (he'.trans ht).ne') },
  { have : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioi $ max e 1),
      ‖t ^ (s - 1) * f t‖ ≤ t ^ ((s - 1) + -a) * d,
    { refine (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ (λ t ht, _)),
      have ht' : 0 < t, from he'.trans ht,
      rw [norm_mul, rpow_add ht', ←norm_of_nonneg (rpow_nonneg_of_nonneg ht'.le (-a)),
        mul_assoc, mul_comm _ d, norm_of_nonneg (rpow_nonneg_of_nonneg ht'.le _)],
      exact mul_le_mul_of_nonneg_left (he t ((le_max_left e 1).trans_lt ht).le)
        (rpow_pos_of_pos ht' _).le },
    refine (has_finite_integral.mul_const _ _).mono' this,
    exact (integrable_on_Ioi_rpow_of_lt (by linarith) he').has_finite_integral }
end

/-- If `f` is a locally integrable real-valued function which is `O(x ^ (-b))` at `0`, then for any
`b < s`, its Mellin transform converges on some right neighbourhood of `0`. -/
lemma mellin_convergent_zero_of_is_O
  {b : ℝ} {f : ℝ → ℝ} (hfc : ae_strongly_measurable f $ volume.restrict (Ioi 0))
  (hf : is_O (𝓝[Ioi 0] 0) f (λ t, t ^ (-b))) {s : ℝ} (hs : b < s) :
  ∃ (c : ℝ), 0 < c ∧ integrable_on (λ t : ℝ, t ^ (s - 1) * f t) (Ioc 0 c) :=
begin
  obtain ⟨d, hd, hd'⟩ := hf.exists_pos,
  simp_rw [is_O_with, eventually_nhds_within_iff, metric.eventually_nhds_iff, gt_iff_lt] at hd',
  obtain ⟨ε, hε, hε'⟩ := hd',
  refine ⟨ε, hε, integrable_on_Ioc_iff_integrable_on_Ioo.mpr ⟨_, _⟩⟩,
  { refine ae_strongly_measurable.mul _ (hfc.mono_set Ioo_subset_Ioi_self),
    refine (continuous_at.continuous_on (λ t ht, _)).ae_strongly_measurable measurable_set_Ioo,
    exact continuous_at_rpow_const _ _ (or.inl ht.1.ne') },
  { apply has_finite_integral.mono',
    { show has_finite_integral (λ t, d * t ^ (s - b - 1)) _,
      refine (integrable.has_finite_integral _).const_mul _,
      rw [←integrable_on, ←integrable_on_Ioc_iff_integrable_on_Ioo,
        ←interval_integrable_iff_integrable_Ioc_of_le hε.le],
      exact interval_integral.interval_integrable_rpow' (by linarith) },
    { refine (ae_restrict_iff' measurable_set_Ioo).mpr (eventually_of_forall $ λ t ht, _),
      rw [mul_comm, norm_mul],
      specialize hε' _ ht.1,
      { rw [dist_eq_norm, sub_zero, norm_of_nonneg (le_of_lt ht.1)],
        exact ht.2 },
      { refine (mul_le_mul_of_nonneg_right hε' (norm_nonneg _)).trans _,
        simp_rw [norm_of_nonneg (rpow_nonneg_of_nonneg (le_of_lt ht.1) _), mul_assoc],
        refine mul_le_mul_of_nonneg_left (le_of_eq _) hd.le,
        rw ←rpow_add ht.1,
        congr' 1,
        abel } } },
end

/-- If `f` is a locally integrable real-valued function on `Ioi 0` which is `O(x ^ (-a))` at `∞`
and `O(x ^ (-b))` at `0`, then its Mellin transform integral converges for `b < s < a`. -/
lemma mellin_convergent_of_is_O_scalar
  {a b : ℝ} {f : ℝ → ℝ} {s : ℝ}
  (hfc : locally_integrable_on f $ Ioi 0)
  (hf_top : is_O at_top f (λ t, t ^ (-a))) (hs_top : s < a)
  (hf_bot : is_O (𝓝[Ioi 0] 0) f (λ t, t ^ (-b))) (hs_bot : b < s) :
  integrable_on (λ t : ℝ, t ^ (s - 1) * f t) (Ioi 0) :=
begin
  obtain ⟨c1, hc1, hc1'⟩ := mellin_convergent_top_of_is_O hfc.ae_strongly_measurable hf_top hs_top,
  obtain ⟨c2, hc2, hc2'⟩ := mellin_convergent_zero_of_is_O hfc.ae_strongly_measurable hf_bot hs_bot,
  have : Ioi 0 = Ioc 0 c2 ∪ Ioc c2 c1 ∪ Ioi c1,
  { rw [union_assoc, Ioc_union_Ioi (le_max_right _ _), Ioc_union_Ioi
    ((min_le_left _ _).trans (le_max_right _ _)), min_eq_left (lt_min hc2 hc1).le] },
  rw [this, integrable_on_union, integrable_on_union],
  refine ⟨⟨hc2', integrable_on_Icc_iff_integrable_on_Ioc.mp _⟩, hc1'⟩,
  refine (hfc.continuous_on_mul _ is_open_Ioi).integrable_on_compact_subset
    (λ t ht, (hc2.trans_le ht.1 : 0 < t)) is_compact_Icc,
  exact continuous_at.continuous_on (λ t ht, continuous_at_rpow_const _ _ $ or.inl $ ne_of_gt ht),
end

lemma mellin_convergent_of_is_O_rpow [normed_space ℂ E]
  {a b : ℝ} {f : ℝ → E} {s : ℂ}
  (hfc : locally_integrable_on f $ Ioi 0)
  (hf_top : is_O at_top f (λ t, t ^ (-a))) (hs_top : s.re < a)
  (hf_bot : is_O (𝓝[Ioi 0] 0) f (λ t, t ^ (-b))) (hs_bot : b < s.re) :
  integrable_on (λ t : ℝ, (t : ℂ) ^ (s - 1) • f t) (Ioi 0) :=
begin
  rw mellin_convergent_iff_norm (subset_refl _) measurable_set_Ioi
    hfc.ae_strongly_measurable,
  exact mellin_convergent_of_is_O_scalar
    hfc.norm hf_top.norm_left hs_top hf_bot.norm_left hs_bot,
end

end mellin_convergent

section mellin_diff

/-- If `f` is `O(x ^ (-a))` at `+∞`, then `log • f` is `O(x ^ (-b))` for every `b < a`. -/
lemma is_O_rpow_top_log_smul [normed_space ℝ E] {a b : ℝ} {f : ℝ → E}
  (hab : b < a) (hf : is_O at_top f (λ t, t ^ (-a))) :
  is_O at_top (λ t : ℝ, t.log • f t) (λ t, t ^ (-b)) :=
begin
  refine ((is_o_log_rpow_at_top (sub_pos.mpr hab)).is_O.smul hf).congr'
    (eventually_of_forall (λ t, by refl))
    ((eventually_gt_at_top 0).mp (eventually_of_forall (λ t ht, _))),
  rw [smul_eq_mul, ←rpow_add ht, ←sub_eq_add_neg, sub_eq_add_neg a, add_sub_cancel'],
end

/-- If `f` is `O(x ^ (-a))` at `+∞`, then `log • f` is `O(x ^ (-b))` for every `a < b`. -/
lemma is_O_rpow_zero_log_smul [normed_space ℝ E] {a b : ℝ} {f : ℝ → E}
  (hab : a < b) (hf : is_O (𝓝[Ioi 0] 0) f (λ t, t ^ (-a))) :
  is_O (𝓝[Ioi 0] 0) (λ t : ℝ, t.log • f t) (λ t, t ^ (-b)) :=
begin
  have : is_o (𝓝[Ioi 0] 0) (λ t : ℝ, t.log) (λ t : ℝ, t ^ (a - b)),
  { refine ((is_o_log_rpow_at_top (sub_pos.mpr hab)).neg_left.comp_tendsto
      tendsto_inv_zero_at_top).congr'
        (eventually_nhds_within_iff.mpr $ eventually_of_forall (λ t ht, _))
        (eventually_nhds_within_iff.mpr $ eventually_of_forall (λ t ht, _)),
    { simp_rw [function.comp_app, ←one_div, log_div one_ne_zero (ne_of_gt ht), real.log_one,
        zero_sub, neg_neg] },
    { simp_rw [function.comp_app, inv_rpow (le_of_lt ht), ←rpow_neg (le_of_lt ht), neg_sub] } },
  refine (this.is_O.smul hf).congr'
    (eventually_of_forall (λ t, by refl))
    (eventually_nhds_within_iff.mpr (eventually_of_forall (λ t ht, _))),
  simp_rw [smul_eq_mul, ←rpow_add ht],
  congr' 1,
  abel,
end

/-- Suppose `f` is locally integrable on `(0, ∞)`, is `O(x ^ (-a))` as `x → ∞`, and is
`O(x ^ (-b))` as `x → 0`. Then its Mellin transform is differentiable on the domain `b < re s < a`,
with derivative equal to the Mellin transform of `log • f`. -/
theorem mellin_has_deriv_of_is_O_rpow [complete_space E] [normed_space ℂ E]
  {a b : ℝ} {f : ℝ → E} {s : ℂ}
  (hfc : locally_integrable_on f $ Ioi 0)
  (hf_top : is_O at_top f (λ t, t ^ (-a))) (hs_top : s.re < a)
  (hf_bot : is_O (𝓝[Ioi 0] 0) f (λ t, t ^ (-b))) (hs_bot : b < s.re) :
  has_deriv_at (mellin f) (mellin (λ t, (↑(t.log) : ℂ) • f t) s) s :=
begin
  let F : ℂ → ℝ → E := λ z t, (t : ℂ) ^ (z - 1) • f t,
  let F' : ℂ → ℝ → E := λ z t, ((t : ℂ) ^ (z - 1) * t.log) • f t,
  have hab : b < a := hs_bot.trans hs_top,
  -- A convenient radius of ball within which we can uniformly bound the derivative.
  obtain ⟨v, hv0, hv1, hv2⟩ : ∃ (v : ℝ), (0 < v) ∧ (v < s.re - b) ∧ (v < a - s.re),
  { obtain ⟨w, hw1, hw2⟩ := exists_between (sub_pos.mpr hs_top),
    obtain ⟨w', hw1', hw2'⟩ := exists_between (sub_pos.mpr hs_bot),
    exact ⟨min w w', lt_min hw1 hw1',
      (min_le_right _ _).trans_lt hw2', (min_le_left _ _).trans_lt hw2⟩ },
  let bound : ℝ → ℝ := λ t : ℝ, (t ^ (s.re + v - 1) + t ^ (s.re - v - 1)) * |t.log| * ‖f t‖,
  have h1 : ∀ᶠ (z : ℂ) in 𝓝 s, ae_strongly_measurable (F z) (volume.restrict $ Ioi 0),
  { refine eventually_of_forall (λ z, ae_strongly_measurable.smul _ hfc.ae_strongly_measurable),
    refine continuous_on.ae_strongly_measurable _ measurable_set_Ioi,
    refine continuous_at.continuous_on (λ t ht, _),
    exact (continuous_at_of_real_cpow_const _ _ (or.inr $ ne_of_gt ht)), },
  have h2 : integrable_on (F s) (Ioi 0),
  { exact mellin_convergent_of_is_O_rpow hfc hf_top hs_top hf_bot hs_bot },
  have h3 : ae_strongly_measurable (F' s) (volume.restrict $ Ioi 0),
  { apply locally_integrable_on.ae_strongly_measurable,
    refine hfc.continuous_on_smul is_open_Ioi ((continuous_at.continuous_on (λ t ht, _)).mul _),
    { exact continuous_at_of_real_cpow_const _ _ (or.inr $ ne_of_gt ht) },
    { refine continuous_of_real.comp_continuous_on _,
      exact continuous_on_log.mono (subset_compl_singleton_iff.mpr not_mem_Ioi_self) } },
  have h4 : (∀ᵐ (t : ℝ) ∂volume.restrict (Ioi 0), ∀ (z : ℂ),
    z ∈ metric.ball s v → ‖F' z t‖ ≤ bound t),
  { refine (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ $ λ t ht z hz, _),
    simp_rw [bound, F', norm_smul, norm_mul, complex.norm_eq_abs (real.log _), complex.abs_of_real,
      mul_assoc],
    refine mul_le_mul_of_nonneg_right _ (mul_nonneg (abs_nonneg _) (norm_nonneg _)),
    rw [complex.norm_eq_abs, abs_cpow_eq_rpow_re_of_pos ht],
    rcases le_or_lt 1 t,
    { refine le_add_of_le_of_nonneg (rpow_le_rpow_of_exponent_le h _)
        (rpow_nonneg_of_nonneg (zero_le_one.trans h) _),
      rw [sub_re, one_re, sub_le_sub_iff_right],
      rw [mem_ball_iff_norm, complex.norm_eq_abs] at hz,
      have hz' := (re_le_abs _).trans hz.le,
      rwa [sub_re, sub_le_iff_le_add'] at hz' },
    { refine le_add_of_nonneg_of_le (rpow_pos_of_pos ht _).le
        (rpow_le_rpow_of_exponent_ge ht h.le _),
      rw [sub_re, one_re, sub_le_iff_le_add, sub_add_cancel],
      rw [mem_ball_iff_norm', complex.norm_eq_abs] at hz,
      have hz' := (re_le_abs _).trans hz.le,
      rwa [sub_re, sub_le_iff_le_add, ←sub_le_iff_le_add'] at hz', } },
  have h5 : integrable_on bound (Ioi 0),
  { simp_rw [bound, add_mul, mul_assoc],
    suffices : ∀ {j : ℝ} (hj : b < j) (hj' : j < a),
      integrable_on (λ (t : ℝ), t ^ (j - 1) * (|log t| * ‖f t‖)) (Ioi 0) volume,
    { refine integrable.add (this _ _) (this _ _),
      all_goals { linarith } },
    { intros j hj hj',
      obtain ⟨w, hw1, hw2⟩ := exists_between hj,
      obtain ⟨w', hw1', hw2'⟩ := exists_between hj',
      refine mellin_convergent_of_is_O_scalar _ _ hw1' _ hw2,
      { simp_rw mul_comm,
        refine hfc.norm.mul_continuous_on _ is_open_Ioi,
        refine continuous.comp_continuous_on continuous_abs (continuous_on_log.mono _),
        exact subset_compl_singleton_iff.mpr not_mem_Ioi_self },
      { refine (is_O_rpow_top_log_smul hw2' hf_top).norm_left.congr' _ (eventually_eq.refl _ _),
        refine (eventually_gt_at_top 0).mp (eventually_of_forall (λ t ht, _)),
        simp only [norm_smul, real.norm_eq_abs] },
      { refine (is_O_rpow_zero_log_smul hw1 hf_bot).norm_left.congr' _ (eventually_eq.refl _ _),
        refine eventually_nhds_within_iff.mpr (eventually_of_forall (λ t ht, _)),
        simp only [norm_smul, real.norm_eq_abs] } } },
  have h6 : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioi 0), ∀ (y : ℂ),
    y ∈ metric.ball s v → has_deriv_at (λ (z : ℂ), F z t) (F' y t) y,
  { dsimp only [F, F'],
    refine (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ $ λ t ht y hy, _),
    have ht' : (t : ℂ) ≠ 0 := of_real_ne_zero.mpr (ne_of_gt ht),
    have u1 : has_deriv_at (λ z : ℂ, (t : ℂ) ^ (z - 1)) (↑t ^ (y - 1) * ↑t.log) y,
    { convert ((has_deriv_at_id' y).sub_const 1).const_cpow (or.inl ht') using 1,
      rw of_real_log (le_of_lt ht),
      ring },
    exact u1.smul_const (f t) },
  simpa only [F', mellin, mul_smul] using
    (has_deriv_at_integral_of_dominated_loc_of_deriv_le hv0 h1 h2 h3 h4 h5 h6).2,
end

/-- Suppose `f` is locally integrable on `(0, ∞)`, is `O(x ^ (-a))` as `x → ∞`, and is
`O(x ^ (-b))` as `x → 0`. Then its Mellin transform is differentiable on the domain `b < re s < a`.
-/
lemma mellin_differentiable_at_of_is_O_rpow [complete_space E] [normed_space ℂ E]
  {a b : ℝ} {f : ℝ → E} {s : ℂ}
  (hfc : locally_integrable_on f $ Ioi 0)
  (hf_top : is_O at_top f (λ t, t ^ (-a))) (hs_top : s.re < a)
  (hf_bot : is_O (𝓝[Ioi 0] 0) f (λ t, t ^ (-b))) (hs_bot : b < s.re) :
  differentiable_at ℂ (mellin f) s :=
(mellin_has_deriv_of_is_O_rpow hfc hf_top hs_top hf_bot hs_bot).differentiable_at

end mellin_diff

section exp_decay

/-- If `f` is `O(exp (-a * x))` at top for some `0 < a`, then it is `O(x ^ b)` for every `b`. -/
lemma is_o_rpow_of_is_O_exp_neg {f : ℝ → E} {a : ℝ} (ha : 0 < a)
  (hf : is_O at_top f (λ t, exp (-a * t))) (b : ℝ) :
  is_o at_top f (λ t, t ^ b) :=
begin
  refine hf.trans_is_o (is_o_of_tendsto' _ _),
  { refine (eventually_gt_at_top 0).mp (eventually_of_forall $ λ t ht h, _),
    rw rpow_eq_zero_iff_of_nonneg ht.le at h,
    exact (ht.ne' h.1).elim },
  { refine (tendsto_exp_mul_div_rpow_at_top (-b) a ha).inv_tendsto_at_top.congr' _,
    refine (eventually_ge_at_top 0).mp (eventually_of_forall $ λ t ht, _),
    dsimp only,
    rw [pi.inv_apply, inv_div, ←inv_div_inv, neg_mul, real.exp_neg, rpow_neg ht, inv_inv] }
end

/-- If `f` is locally integrable, decays exponentially at infinity, and is `O(x ^ (-b))` at 0, then
its Mellin transform converges for `b < s.re`. -/
lemma mellin_convergent_of_is_O_rpow_exp [normed_space ℂ E]
  {a b : ℝ} (ha : 0 < a) {f : ℝ → E} {s : ℂ}
  (hfc : locally_integrable_on f $ Ioi 0)
  (hf_top : is_O at_top f (λ t, exp (-a * t)))
  (hf_bot : is_O (𝓝[Ioi 0] 0) f (λ t, t ^ (-b))) (hs_bot : b < s.re) :
  integrable_on (λ t : ℝ, (t : ℂ) ^ (s - 1) • f t) (Ioi 0) :=
mellin_convergent_of_is_O_rpow hfc
  (is_o_rpow_of_is_O_exp_neg ha hf_top _).is_O (lt_add_one _) hf_bot hs_bot

/-- If `f` is locally integrable, decays exponentially at infinity, and is `O(x ^ (-b))` at 0, then
its Mellin transform is holomorphic on `b < s.re`. -/
lemma mellin_differentiable_at_of_is_O_rpow_exp [complete_space E] [normed_space ℂ E]
  {a b : ℝ} (ha : 0 < a) {f : ℝ → E} {s : ℂ}
  (hfc : locally_integrable_on f $ Ioi 0)
  (hf_top : is_O at_top f (λ t, exp (-a * t)))
  (hf_bot : is_O (𝓝[Ioi 0] 0) f (λ t, t ^ (-b))) (hs_bot : b < s.re) :
  differentiable_at ℂ (mellin f) s :=
mellin_differentiable_at_of_is_O_rpow hfc
  (is_o_rpow_of_is_O_exp_neg ha hf_top _).is_O (lt_add_one _) hf_bot hs_bot

end exp_decay
