/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/

import measure_theory.function.conditional_expectation.indicator
import measure_theory.function.uniform_integrable
import measure_theory.decomposition.radon_nikodym

/-!

# Conditional expectation of real-valued functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves some results regarding the conditional expectation of real-valued functions.

## Main results

* `measure_theory.rn_deriv_ae_eq_condexp`: the conditional expectation `μ[f | m]` is equal to the
  Radon-Nikodym derivative of `fμ` restricted on `m` with respect to `μ` restricted on `m`.
* `measure_theory.integrable.uniform_integrable_condexp`: the conditional expectation of a function
  form a uniformly integrable class.
* `measure_theory.condexp_strongly_measurable_mul`: the pull-out property of the conditional
  expectation.

-/

noncomputable theory
open topological_space measure_theory.Lp filter continuous_linear_map
open_locale nnreal ennreal topology big_operators measure_theory

namespace measure_theory

variables {α : Type*} {m m0 : measurable_space α} {μ : measure α}

lemma rn_deriv_ae_eq_condexp {hm : m ≤ m0} [hμm : sigma_finite (μ.trim hm)] {f : α → ℝ}
  (hf : integrable f μ) :
  signed_measure.rn_deriv ((μ.with_densityᵥ f).trim hm) (μ.trim hm) =ᵐ[μ] μ[f | m] :=
begin
  refine ae_eq_condexp_of_forall_set_integral_eq hm hf _ _ _,
  { exact λ _ _ _, (integrable_of_integrable_trim hm (signed_measure.integrable_rn_deriv
      ((μ.with_densityᵥ f).trim hm) (μ.trim hm))).integrable_on },
  { intros s hs hlt,
    conv_rhs { rw [← hf.with_densityᵥ_trim_eq_integral hm hs,
      ← signed_measure.with_densityᵥ_rn_deriv_eq ((μ.with_densityᵥ f).trim hm) (μ.trim hm)
        (hf.with_densityᵥ_trim_absolutely_continuous hm)], },
    rw [with_densityᵥ_apply
        (signed_measure.integrable_rn_deriv ((μ.with_densityᵥ f).trim hm) (μ.trim hm)) hs,
      ← set_integral_trim hm _ hs],
    exact (signed_measure.measurable_rn_deriv _ _).strongly_measurable },
  { exact strongly_measurable.ae_strongly_measurable'
      (signed_measure.measurable_rn_deriv _ _).strongly_measurable },
end

-- TODO: the following couple of lemmas should be generalized and proved using Jensen's inequality
-- for the conditional expectation (not in mathlib yet) .
lemma snorm_one_condexp_le_snorm (f : α → ℝ) :
  snorm (μ[f | m]) 1 μ ≤ snorm f 1 μ :=
begin
  by_cases hf : integrable f μ,
  swap, { rw [condexp_undef hf, snorm_zero], exact zero_le _ },
  by_cases hm : m ≤ m0,
  swap, { rw [condexp_of_not_le hm, snorm_zero], exact zero_le _ },
  by_cases hsig : sigma_finite (μ.trim hm),
  swap, { rw [condexp_of_not_sigma_finite hm hsig, snorm_zero], exact zero_le _ },
  calc snorm (μ[f | m]) 1 μ ≤ snorm (μ[|f| | m]) 1 μ :
  begin
    refine snorm_mono_ae _,
    filter_upwards [@condexp_mono _ m m0 _ _ _ _ _ _ _ _ hf hf.abs
        (@ae_of_all _ m0 _ μ (λ x, le_abs_self (f x) : ∀ x, f x ≤ |f x|)),
      eventually_le.trans (condexp_neg f).symm.le
        (@condexp_mono _ m m0 _ _ _ _ _ _ _  _ hf.neg hf.abs
        (@ae_of_all _ m0 _ μ (λ x, neg_le_abs_self (f x) : ∀ x, -f x ≤ |f x|)))] with x hx₁ hx₂,
    exact abs_le_abs hx₁ hx₂,
  end
    ... = snorm f 1 μ :
  begin
    rw [snorm_one_eq_lintegral_nnnorm, snorm_one_eq_lintegral_nnnorm,
      ← ennreal.to_real_eq_to_real (ne_of_lt integrable_condexp.2) (ne_of_lt hf.2),
      ← integral_norm_eq_lintegral_nnnorm
        (strongly_measurable_condexp.mono hm).ae_strongly_measurable,
      ← integral_norm_eq_lintegral_nnnorm hf.1],
    simp_rw [real.norm_eq_abs],
    rw ← @integral_condexp _ _ _ _ _ m m0 μ _ hm hsig hf.abs,
    refine integral_congr_ae _,
    have : 0 ≤ᵐ[μ] μ[|f| | m],
    { rw ← @condexp_zero α ℝ _ _ _ m m0 μ,
      exact condexp_mono (integrable_zero _ _ _) hf.abs
        (@ae_of_all _ m0 _ μ (λ x, abs_nonneg (f x) : ∀ x, 0 ≤ |f x|)) },
    filter_upwards [this] with x hx,
    exact abs_eq_self.2 hx
  end
end

lemma integral_abs_condexp_le (f : α → ℝ) :
  ∫ x, |μ[f | m] x| ∂μ ≤ ∫ x, |f x| ∂μ :=
begin
  by_cases hm : m ≤ m0,
  swap,
  { simp_rw [condexp_of_not_le hm, pi.zero_apply, abs_zero, integral_zero],
    exact integral_nonneg (λ x, abs_nonneg _) },
  by_cases hfint : integrable f μ,
  swap,
  { simp only [condexp_undef hfint, pi.zero_apply, abs_zero, integral_const,
      algebra.id.smul_eq_mul, mul_zero],
    exact integral_nonneg (λ x, abs_nonneg _) },
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae],
  { rw ennreal.to_real_le_to_real;
    simp_rw [← real.norm_eq_abs, of_real_norm_eq_coe_nnnorm],
    { rw [← snorm_one_eq_lintegral_nnnorm, ← snorm_one_eq_lintegral_nnnorm],
      exact snorm_one_condexp_le_snorm _ },
    { exact ne_of_lt integrable_condexp.2 },
    { exact ne_of_lt hfint.2 } },
  { exact eventually_of_forall (λ x, abs_nonneg _) },
  { simp_rw ← real.norm_eq_abs,
    exact hfint.1.norm },
  { exact eventually_of_forall (λ x, abs_nonneg _) },
  { simp_rw ← real.norm_eq_abs,
    exact (strongly_measurable_condexp.mono hm).ae_strongly_measurable.norm }
end

lemma set_integral_abs_condexp_le {s : set α} (hs : measurable_set[m] s) (f : α → ℝ) :
  ∫ x in s, |μ[f | m] x| ∂μ ≤ ∫ x in s, |f x| ∂μ :=
begin
  by_cases hnm : m ≤ m0,
  swap,
  { simp_rw [condexp_of_not_le hnm, pi.zero_apply, abs_zero, integral_zero],
    exact integral_nonneg (λ x, abs_nonneg _) },
  by_cases hfint : integrable f μ,
  swap,
  { simp only [condexp_undef hfint, pi.zero_apply, abs_zero, integral_const,
      algebra.id.smul_eq_mul, mul_zero],
    exact integral_nonneg (λ x, abs_nonneg _) },
  have : ∫ x in s, |μ[f | m] x| ∂μ = ∫ x, |μ[s.indicator f | m] x| ∂μ,
  { rw ← integral_indicator,
    swap, { exact hnm _ hs },
    refine integral_congr_ae _,
    have : (λ x, |μ[s.indicator f | m] x|) =ᵐ[μ] λ x, |s.indicator (μ[f | m]) x| :=
      eventually_eq.fun_comp (condexp_indicator hfint hs) _,
    refine eventually_eq.trans (eventually_of_forall $ λ x, _) this.symm,
    rw [← real.norm_eq_abs, norm_indicator_eq_indicator_norm],
    refl },
  rw [this, ← integral_indicator],
  swap, { exact hnm _ hs },
  refine (integral_abs_condexp_le _).trans (le_of_eq $ integral_congr_ae $
    eventually_of_forall $ λ x, _),
  rw [← real.norm_eq_abs, norm_indicator_eq_indicator_norm],
  refl,
end

/-- If the real valued function `f` is bounded almost everywhere by `R`, then so is its conditional
expectation. -/
lemma ae_bdd_condexp_of_ae_bdd {R : ℝ≥0} {f : α → ℝ}
  (hbdd : ∀ᵐ x ∂μ, |f x| ≤ R) :
  ∀ᵐ x ∂μ, |μ[f | m] x| ≤ R :=
begin
  by_cases hnm : m ≤ m0,
  swap,
  { simp_rw [condexp_of_not_le hnm, pi.zero_apply, abs_zero],
    refine eventually_of_forall (λ x, R.coe_nonneg) },
  by_cases hfint : integrable f μ,
  swap,
  { simp_rw [condexp_undef hfint],
    filter_upwards [hbdd] with x hx,
    rw [pi.zero_apply, abs_zero],
    exact (abs_nonneg _).trans hx },
  by_contra h,
  change μ _ ≠ 0 at h,
  simp only [← zero_lt_iff, set.compl_def, set.mem_set_of_eq, not_le] at h,
  suffices : (μ {x | ↑R < |μ[f | m] x|}).to_real * ↑R < (μ {x | ↑R < |μ[f | m] x|}).to_real * ↑R,
  { exact this.ne rfl },
  refine lt_of_lt_of_le (set_integral_gt_gt R.coe_nonneg _ _ h.ne.symm) _,
  { simp_rw [← real.norm_eq_abs],
    exact (strongly_measurable_condexp.mono hnm).measurable.norm },
  { exact integrable_condexp.abs.integrable_on },
  refine (set_integral_abs_condexp_le _ _).trans _,
  { simp_rw [← real.norm_eq_abs],
    exact @measurable_set_lt _ _ _ _ _ m _ _ _ _ _ measurable_const
      strongly_measurable_condexp.norm.measurable },
  simp only [← smul_eq_mul, ← set_integral_const, nnreal.val_eq_coe,
    is_R_or_C.coe_real_eq_id, id.def],
  refine set_integral_mono_ae hfint.abs.integrable_on _ _,
  { refine ⟨ae_strongly_measurable_const, lt_of_le_of_lt _
      (integrable_condexp.integrable_on : integrable_on (μ[f | m]) {x | ↑R < |μ[f | m] x|} μ).2⟩,
    refine set_lintegral_mono (measurable.nnnorm _).coe_nnreal_ennreal
      (strongly_measurable_condexp.mono hnm).measurable.nnnorm.coe_nnreal_ennreal (λ x hx, _),
    { exact measurable_const },
    { rw [ennreal.coe_le_coe, real.nnnorm_of_nonneg R.coe_nonneg],
      exact subtype.mk_le_mk.2 (le_of_lt hx) } },
  { exact hbdd },
end

/-- Given a integrable function `g`, the conditional expectations of `g` with respect to
a sequence of sub-σ-algebras is uniformly integrable. -/
lemma integrable.uniform_integrable_condexp {ι : Type*} [is_finite_measure μ]
  {g : α → ℝ} (hint : integrable g μ) {ℱ : ι → measurable_space α} (hℱ : ∀ i, ℱ i ≤ m0) :
  uniform_integrable (λ i, μ[g | ℱ i]) 1 μ :=
begin
  have hmeas : ∀ n, ∀ C, measurable_set {x | C ≤ ‖μ[g | ℱ n] x‖₊} :=
    λ n C, measurable_set_le measurable_const
      (strongly_measurable_condexp.mono (hℱ n)).measurable.nnnorm,
  have hg : mem_ℒp g 1 μ := mem_ℒp_one_iff_integrable.2 hint,
  refine uniform_integrable_of le_rfl ennreal.one_ne_top
    (λ n, (strongly_measurable_condexp.mono (hℱ n)).ae_strongly_measurable) (λ ε hε, _),
  by_cases hne : snorm g 1 μ = 0,
  { rw snorm_eq_zero_iff hg.1 one_ne_zero at hne,
    refine ⟨0, λ n, (le_of_eq $ (snorm_eq_zero_iff
      ((strongly_measurable_condexp.mono (hℱ n)).ae_strongly_measurable.indicator (hmeas n 0))
      one_ne_zero).2 _).trans (zero_le _)⟩,
    filter_upwards [@condexp_congr_ae _ _ _ _ _ (ℱ n) m0 μ _ _ hne] with x hx,
    simp only [zero_le', set.set_of_true, set.indicator_univ, pi.zero_apply, hx, condexp_zero] },
  obtain ⟨δ, hδ, h⟩ := hg.snorm_indicator_le μ le_rfl ennreal.one_ne_top hε,
  set C : ℝ≥0 := ⟨δ, hδ.le⟩⁻¹ * (snorm g 1 μ).to_nnreal with hC,
  have hCpos : 0 < C :=
    mul_pos (inv_pos.2 hδ) (ennreal.to_nnreal_pos hne hg.snorm_lt_top.ne),
  have : ∀ n, μ {x : α | C ≤ ‖μ[g | ℱ n] x‖₊} ≤ ennreal.of_real δ,
  { intro n,
    have := mul_meas_ge_le_pow_snorm' μ one_ne_zero ennreal.one_ne_top
      ((@strongly_measurable_condexp _ _ _ _ _ (ℱ n) _ μ g).mono
        (hℱ n)).ae_strongly_measurable C,
    rw [ennreal.one_to_real, ennreal.rpow_one, ennreal.rpow_one, mul_comm,
      ← ennreal.le_div_iff_mul_le (or.inl (ennreal.coe_ne_zero.2 hCpos.ne.symm))
        (or.inl ennreal.coe_lt_top.ne)] at this,
    simp_rw [ennreal.coe_le_coe] at this,
    refine this.trans _,
    rw [ennreal.div_le_iff_le_mul (or.inl (ennreal.coe_ne_zero.2 hCpos.ne.symm))
        (or.inl ennreal.coe_lt_top.ne), hC, nonneg.inv_mk, ennreal.coe_mul,
      ennreal.coe_to_nnreal hg.snorm_lt_top.ne, ← mul_assoc, ← ennreal.of_real_eq_coe_nnreal,
      ← ennreal.of_real_mul hδ.le, mul_inv_cancel hδ.ne.symm, ennreal.of_real_one, one_mul],
    exact snorm_one_condexp_le_snorm _ },
  refine ⟨C, λ n, le_trans _ (h {x : α | C ≤ ‖μ[g | ℱ n] x‖₊} (hmeas n C) (this n))⟩,
  have hmeasℱ : measurable_set[ℱ n] {x : α | C ≤ ‖μ[g | ℱ n] x‖₊} :=
    @measurable_set_le _ _ _ _ _ (ℱ n) _ _ _ _ _ measurable_const
      (@measurable.nnnorm _ _ _ _ _ (ℱ n) _ strongly_measurable_condexp.measurable),
  rw ← snorm_congr_ae (condexp_indicator hint hmeasℱ),
  exact snorm_one_condexp_le_snorm _,
end

section pull_out
-- TODO: this section could be generalized beyond multiplication, to any bounded bilinear map.

/-- Auxiliary lemma for `condexp_measurable_mul`. -/
lemma condexp_strongly_measurable_simple_func_mul (hm : m ≤ m0)
  (f : @simple_func α m ℝ) {g : α → ℝ} (hg : integrable g μ) :
  μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
begin
  have : ∀ s c (f : α → ℝ), set.indicator s (function.const α c) * f = s.indicator (c • f),
  { intros s c f,
    ext1 x,
    by_cases hx : x ∈ s,
    { simp only [hx, pi.mul_apply, set.indicator_of_mem, pi.smul_apply, algebra.id.smul_eq_mul] },
    { simp only [hx, pi.mul_apply, set.indicator_of_not_mem, not_false_iff, zero_mul], }, },
  refine @simple_func.induction _ _ m _ _ (λ c s hs, _) (λ g₁ g₂ h_disj h_eq₁ h_eq₂, _) f,
  { simp only [simple_func.const_zero, simple_func.coe_piecewise, simple_func.coe_const,
      simple_func.coe_zero, set.piecewise_eq_indicator],
    rw [this, this],
    refine (condexp_indicator (hg.smul c) hs).trans _,
    filter_upwards [@condexp_smul α ℝ ℝ _ _ _ _ _ m m0 μ c g] with x hx,
    classical,
    simp_rw [set.indicator_apply, hx], },
  { have h_add := @simple_func.coe_add _ _ m _ g₁ g₂,
    calc μ[⇑(g₁ + g₂) * g|m] =ᵐ[μ] μ[(⇑g₁ + ⇑g₂) * g|m] :
      by { refine condexp_congr_ae (eventually_eq.mul _ eventually_eq.rfl), rw h_add, }
    ... =ᵐ[μ] μ[⇑g₁ * g|m] + μ[⇑g₂ * g|m] :
      by { rw add_mul, exact condexp_add (hg.simple_func_mul' hm _) (hg.simple_func_mul' hm _), }
    ... =ᵐ[μ] ⇑g₁ * μ[g|m] + ⇑g₂ * μ[g|m] : eventually_eq.add h_eq₁ h_eq₂
    ... =ᵐ[μ] ⇑(g₁ + g₂) * μ[g|m] : by rw [h_add, add_mul], },
end

lemma condexp_strongly_measurable_mul_of_bound (hm : m ≤ m0) [is_finite_measure μ]
  {f g : α → ℝ} (hf : strongly_measurable[m] f) (hg : integrable g μ) (c : ℝ)
  (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
  μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
begin
  let fs := hf.approx_bounded c,
  have hfs_tendsto : ∀ᵐ x ∂μ, tendsto (λ n, fs n x) at_top (𝓝 (f x)),
    from hf.tendsto_approx_bounded_ae hf_bound,
  by_cases hμ : μ = 0,
  { simp only [hμ, ae_zero], },
  haveI : μ.ae.ne_bot, by simp only [hμ, ae_ne_bot, ne.def, not_false_iff],
  have hc : 0 ≤ c,
  { have h_exists : ∃ x, ‖f x‖ ≤ c := eventually.exists hf_bound,
    exact (norm_nonneg _).trans h_exists.some_spec, },
  have hfs_bound : ∀ n x, ‖fs n x‖ ≤ c := hf.norm_approx_bounded_le hc,
  have hn_eq : ∀ n, μ[fs n * g | m] =ᵐ[μ] fs n * μ[g | m],
    from λ n, condexp_strongly_measurable_simple_func_mul hm _ hg,
  have : μ[f * μ[g|m]|m] = f * μ[g|m],
  { refine condexp_of_strongly_measurable hm (hf.mul strongly_measurable_condexp) _,
    exact integrable_condexp.bdd_mul' ((hf.mono hm).ae_strongly_measurable) hf_bound, },
  rw ← this,
  refine tendsto_condexp_unique (λ n x, fs n x * g x) (λ n x, fs n x * μ[g|m] x) (f * g)
    (f * μ[g|m]) _ _ _ _ (λ x, c * ‖g x‖) _ (λ x, c * ‖μ[g|m] x‖) _ _ _ _,
  { exact λ n, hg.bdd_mul'
      ((simple_func.strongly_measurable (fs n)).mono hm).ae_strongly_measurable
      (eventually_of_forall (hfs_bound n)), },
  { exact λ n, integrable_condexp.bdd_mul'
      ((simple_func.strongly_measurable (fs n)).mono hm).ae_strongly_measurable
      (eventually_of_forall (hfs_bound n)), },
  { filter_upwards [hfs_tendsto] with x hx,
    rw pi.mul_apply,
    exact tendsto.mul hx tendsto_const_nhds, },
  { filter_upwards [hfs_tendsto] with x hx,
    rw pi.mul_apply,
    exact tendsto.mul hx tendsto_const_nhds, },
  { exact hg.norm.const_mul c, },
  { exact integrable_condexp.norm.const_mul c, },
  { refine λ n, eventually_of_forall (λ x, _),
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hfs_bound n x) (norm_nonneg _)), },
  { refine λ n, eventually_of_forall (λ x, _),
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hfs_bound n x) (norm_nonneg _)), },
  { intros n,
    simp_rw ← pi.mul_apply,
    refine (condexp_strongly_measurable_simple_func_mul hm _ hg).trans _,
    rw condexp_of_strongly_measurable hm
      ((simple_func.strongly_measurable _).mul strongly_measurable_condexp) _,
    { apply_instance, },
    { apply_instance, },
    exact integrable_condexp.bdd_mul'
      ((simple_func.strongly_measurable (fs n)).mono hm).ae_strongly_measurable
      (eventually_of_forall (hfs_bound n)), },
end

lemma condexp_strongly_measurable_mul_of_bound₀ (hm : m ≤ m0) [is_finite_measure μ]
  {f g : α → ℝ} (hf : ae_strongly_measurable' m f μ) (hg : integrable g μ) (c : ℝ)
  (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
  μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
begin
  have : μ[f * g | m] =ᵐ[μ] μ[hf.mk f * g | m],
    from condexp_congr_ae (eventually_eq.mul hf.ae_eq_mk eventually_eq.rfl),
  refine this.trans _,
  have : f * μ[g | m] =ᵐ[μ] hf.mk f * μ[g | m] := eventually_eq.mul hf.ae_eq_mk eventually_eq.rfl,
  refine eventually_eq.trans _ this.symm,
  refine condexp_strongly_measurable_mul_of_bound hm hf.strongly_measurable_mk hg c _,
  filter_upwards [hf_bound, hf.ae_eq_mk] with x hxc hx_eq,
  rw ← hx_eq,
  exact hxc,
end

/-- Pull-out property of the conditional expectation. -/
lemma condexp_strongly_measurable_mul {f g : α → ℝ} (hf : strongly_measurable[m] f)
  (hfg : integrable (f * g) μ) (hg : integrable g μ) :
  μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
begin
  by_cases hm : m ≤ m0, swap, { simp_rw condexp_of_not_le hm, rw mul_zero, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { simp_rw condexp_of_not_sigma_finite hm hμm, rw mul_zero, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  obtain ⟨sets, sets_prop, h_univ⟩ := hf.exists_spanning_measurable_set_norm_le hm μ,
  simp_rw forall_and_distrib at sets_prop,
  obtain ⟨h_meas, h_finite, h_norm⟩ := sets_prop,

  suffices : ∀ n, ∀ᵐ x ∂μ, x ∈ sets n → μ[f * g|m] x = f x * μ[g|m] x,
  { rw ← ae_all_iff at this,
    filter_upwards [this] with x hx,
    rw pi.mul_apply,
    obtain ⟨i, hi⟩ : ∃ i, x ∈ sets i,
    { have h_mem : x ∈ ⋃ i, sets i,
      { rw h_univ, exact set.mem_univ _, },
      simpa using h_mem, },
    exact hx i hi, },
  refine λ n, ae_imp_of_ae_restrict _,
  suffices : (μ.restrict (sets n))[f * g | m]
    =ᵐ[μ.restrict (sets n)] f * (μ.restrict (sets n))[g | m],
  { simp_rw ← pi.mul_apply,
    refine (condexp_restrict_ae_eq_restrict hm (h_meas n) hfg).symm.trans _,
    exact this.trans (eventually_eq.rfl.mul (condexp_restrict_ae_eq_restrict hm (h_meas n) hg)), },
  suffices : (μ.restrict (sets n))[((sets n).indicator f) * g | m]
    =ᵐ[μ.restrict (sets n)] ((sets n).indicator f) * (μ.restrict (sets n))[g | m],
  { refine eventually_eq.trans _ (this.trans _),
    { exact condexp_congr_ae
        ((indicator_ae_eq_restrict (hm _ (h_meas n))).symm.mul eventually_eq.rfl), },
    { exact (indicator_ae_eq_restrict (hm _ (h_meas n))).mul eventually_eq.rfl, }, },
  haveI : is_finite_measure (μ.restrict (sets n)),
  { constructor,
    rw measure.restrict_apply_univ,
    exact h_finite n, },
  refine condexp_strongly_measurable_mul_of_bound hm (hf.indicator (h_meas n)) hg.integrable_on n _,
  refine eventually_of_forall (λ x, _),
  by_cases hxs : x ∈ sets n,
  { simp only [hxs, set.indicator_of_mem],
    exact h_norm n x hxs, },
  { simp only [hxs, set.indicator_of_not_mem, not_false_iff, _root_.norm_zero, nat.cast_nonneg], },
end

/-- Pull-out property of the conditional expectation. -/
lemma condexp_strongly_measurable_mul₀ {f g : α → ℝ} (hf : ae_strongly_measurable' m f μ)
  (hfg : integrable (f * g) μ) (hg : integrable g μ) :
  μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
begin
  have : μ[f * g | m] =ᵐ[μ] μ[hf.mk f * g | m],
    from condexp_congr_ae (eventually_eq.mul hf.ae_eq_mk eventually_eq.rfl),
  refine this.trans _,
  have : f * μ[g | m] =ᵐ[μ] hf.mk f * μ[g | m] := eventually_eq.mul hf.ae_eq_mk eventually_eq.rfl,
  refine eventually_eq.trans _ this.symm,
  refine condexp_strongly_measurable_mul hf.strongly_measurable_mk _ hg,
  refine (integrable_congr _).mp hfg,
  exact eventually_eq.mul hf.ae_eq_mk eventually_eq.rfl,
end

end pull_out

end measure_theory
