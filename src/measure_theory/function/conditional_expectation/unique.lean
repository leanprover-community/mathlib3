/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.function.conditional_expectation.ae_measurable

/-!
# Uniqueness of the conditional expectation

Two Lp functions `f, g` which are almost everywhere strongly measurable with respect to a σ-algebra
`m` and verify `∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ` for all `m`-measurable sets `s` are equal
almost everywhere. This proves the uniqueness of the conditional expectation, which is not yet
defined in this file but is introduced in `measure_theory.function.conditional_expectation.basic`.

## Main statements

* `Lp.ae_eq_of_forall_set_integral_eq'`: two `Lp` functions verifying the equality of integrals
  defining the conditional expectation are equal.
* `ae_eq_of_forall_set_integral_eq_of_sigma_finite'`: two functions verifying the equality of
  integrals defining the conditional expectation are equal almost everywhere.
  Requires `[sigma_finite (μ.trim hm)]`.

-/

open_locale ennreal measure_theory

namespace measure_theory

variables {α E' F' 𝕜 : Type*} {p : ℝ≥0∞}
  {m m0 : measurable_space α} {μ : measure α}
  [is_R_or_C 𝕜] -- 𝕜 for ℝ or ℂ
  -- E' for an inner product space on which we compute integrals
  [normed_add_comm_group E'] [inner_product_space 𝕜 E']
  [complete_space E'] [normed_space ℝ E']
  -- F' for integrals on a Lp submodule
  [normed_add_comm_group F'] [normed_space 𝕜 F'] [normed_space ℝ F'] [complete_space F']

section uniqueness_of_conditional_expectation

/-! ## Uniqueness of the conditional expectation -/

lemma Lp_meas.ae_eq_zero_of_forall_set_integral_eq_zero
  (hm : m ≤ m0) (f : Lp_meas E' 𝕜 m p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  obtain ⟨g, hg_sm, hfg⟩ := Lp_meas.ae_fin_strongly_measurable' hm f hp_ne_zero hp_ne_top,
  refine hfg.trans _,
  refine ae_eq_zero_of_forall_set_integral_eq_of_fin_strongly_measurable_trim hm _ _ hg_sm,
  { intros s hs hμs,
    have hfg_restrict : f =ᵐ[μ.restrict s] g, from ae_restrict_of_ae hfg,
    rw [integrable_on, integrable_congr hfg_restrict.symm],
    exact hf_int_finite s hs hμs, },
  { intros s hs hμs,
    have hfg_restrict : f =ᵐ[μ.restrict s] g, from ae_restrict_of_ae hfg,
    rw integral_congr_ae hfg_restrict.symm,
    exact hf_zero s hs hμs, },
end

include 𝕜
variables (𝕜)

lemma Lp.ae_eq_zero_of_forall_set_integral_eq_zero'
  (hm : m ≤ m0) (f : Lp E' p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  (hf_meas : ae_strongly_measurable' m f μ) :
  f =ᵐ[μ] 0 :=
begin
  let f_meas : Lp_meas E' 𝕜 m p μ := ⟨f, hf_meas⟩,
  have hf_f_meas : f =ᵐ[μ] f_meas, by simp only [coe_fn_coe_base', subtype.coe_mk],
  refine hf_f_meas.trans _,
  refine Lp_meas.ae_eq_zero_of_forall_set_integral_eq_zero hm f_meas hp_ne_zero hp_ne_top _ _,
  { intros s hs hμs,
    have hfg_restrict : f =ᵐ[μ.restrict s] f_meas, from ae_restrict_of_ae hf_f_meas,
    rw [integrable_on, integrable_congr hfg_restrict.symm],
    exact hf_int_finite s hs hμs, },
  { intros s hs hμs,
    have hfg_restrict : f =ᵐ[μ.restrict s] f_meas, from ae_restrict_of_ae hf_f_meas,
    rw integral_congr_ae hfg_restrict.symm,
    exact hf_zero s hs hμs, },
end

/-- **Uniqueness of the conditional expectation** -/
lemma Lp.ae_eq_of_forall_set_integral_eq'
  (hm : m ≤ m0) (f g : Lp E' p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on g s μ)
  (hfg : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
  (hf_meas : ae_strongly_measurable' m f μ) (hg_meas : ae_strongly_measurable' m g μ) :
  f =ᵐ[μ] g :=
begin
  suffices h_sub : ⇑(f-g) =ᵐ[μ] 0,
    by { rw ← sub_ae_eq_zero, exact (Lp.coe_fn_sub f g).symm.trans h_sub, },
  have hfg' : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, (f - g) x ∂μ = 0,
  { intros s hs hμs,
    rw integral_congr_ae (ae_restrict_of_ae (Lp.coe_fn_sub f g)),
    rw integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs),
    exact sub_eq_zero.mpr (hfg s hs hμs), },
  have hfg_int : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on ⇑(f-g) s μ,
  { intros s hs hμs,
    rw [integrable_on, integrable_congr (ae_restrict_of_ae (Lp.coe_fn_sub f g))],
    exact (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs), },
  have hfg_meas : ae_strongly_measurable' m ⇑(f - g) μ,
    from ae_strongly_measurable'.congr (hf_meas.sub hg_meas) (Lp.coe_fn_sub f g).symm,
  exact Lp.ae_eq_zero_of_forall_set_integral_eq_zero' 𝕜 hm (f-g) hp_ne_zero hp_ne_top hfg_int hfg'
    hfg_meas,
end

variables {𝕜}
omit 𝕜

lemma ae_eq_of_forall_set_integral_eq_of_sigma_finite' (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  {f g : α → F'}
  (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on g s μ)
  (hfg_eq : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
  (hfm : ae_strongly_measurable' m f μ) (hgm : ae_strongly_measurable' m g μ) :
  f =ᵐ[μ] g :=
begin
  rw ← ae_eq_trim_iff_of_ae_strongly_measurable' hm hfm hgm,
  have hf_mk_int_finite : ∀ s, measurable_set[m] s → μ.trim hm s < ∞ →
    @integrable_on _ _ m _ (hfm.mk f) s (μ.trim hm),
  { intros s hs hμs,
    rw trim_measurable_set_eq hm hs at hμs,
    rw [integrable_on, restrict_trim hm _ hs],
    refine integrable.trim hm _ hfm.strongly_measurable_mk,
    exact integrable.congr (hf_int_finite s hs hμs) (ae_restrict_of_ae hfm.ae_eq_mk), },
  have hg_mk_int_finite : ∀ s, measurable_set[m] s → μ.trim hm s < ∞ →
    @integrable_on _ _ m _ (hgm.mk g) s (μ.trim hm),
  { intros s hs hμs,
    rw trim_measurable_set_eq hm hs at hμs,
    rw [integrable_on, restrict_trim hm _ hs],
    refine integrable.trim hm _ hgm.strongly_measurable_mk,
    exact integrable.congr (hg_int_finite s hs hμs) (ae_restrict_of_ae hgm.ae_eq_mk), },
  have hfg_mk_eq : ∀ s : set α, measurable_set[m] s → μ.trim hm s < ∞ →
    ∫ x in s, (hfm.mk f x) ∂(μ.trim hm) = ∫ x in s, (hgm.mk g x) ∂(μ.trim hm),
  { intros s hs hμs,
    rw trim_measurable_set_eq hm hs at hμs,
    rw [restrict_trim hm _ hs, ← integral_trim hm hfm.strongly_measurable_mk,
      ← integral_trim hm hgm.strongly_measurable_mk,
      integral_congr_ae (ae_restrict_of_ae hfm.ae_eq_mk.symm),
      integral_congr_ae (ae_restrict_of_ae hgm.ae_eq_mk.symm)],
    exact hfg_eq s hs hμs, },
  exact ae_eq_of_forall_set_integral_eq_of_sigma_finite hf_mk_int_finite hg_mk_int_finite hfg_mk_eq,
end

end uniqueness_of_conditional_expectation


section integral_norm_le

variables {s : set α}

/-- Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫ x in s, ‖g x‖ ∂μ ≤ ∫ x in s, ‖f x‖ ∂μ` on all `m`-measurable sets with finite measure. -/
lemma integral_norm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ}
  (hf : strongly_measurable f) (hfi : integrable_on f s μ)
  (hg : strongly_measurable[m] g) (hgi : integrable_on g s μ)
  (hgf : ∀ t, measurable_set[m] t → μ t < ∞ → ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ)
  (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
  ∫ x in s, ‖g x‖ ∂μ ≤ ∫ x in s, ‖f x‖ ∂μ :=
begin
  rw [integral_norm_eq_pos_sub_neg hgi, integral_norm_eq_pos_sub_neg hfi],
  have h_meas_nonneg_g : measurable_set[m] {x | 0 ≤ g x},
    from (@strongly_measurable_const _ _ m _ _).measurable_set_le hg,
  have h_meas_nonneg_f : measurable_set {x | 0 ≤ f x},
    from strongly_measurable_const.measurable_set_le hf,
  have h_meas_nonpos_g : measurable_set[m] {x | g x ≤ 0},
    from hg.measurable_set_le (@strongly_measurable_const _ _ m _ _),
  have h_meas_nonpos_f : measurable_set {x | f x ≤ 0},
    from hf.measurable_set_le strongly_measurable_const,
  refine sub_le_sub _ _,
  { rw [measure.restrict_restrict (hm _ h_meas_nonneg_g),
      measure.restrict_restrict h_meas_nonneg_f,
      hgf _ (@measurable_set.inter α m _ _ h_meas_nonneg_g hs)
        ((measure_mono (set.inter_subset_right _ _)).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← measure.restrict_restrict (hm _ h_meas_nonneg_g),
      ← measure.restrict_restrict h_meas_nonneg_f],
    exact set_integral_le_nonneg (hm _ h_meas_nonneg_g) hf hfi, },
  { rw [measure.restrict_restrict (hm _ h_meas_nonpos_g),
      measure.restrict_restrict h_meas_nonpos_f,
      hgf _ (@measurable_set.inter α m _ _ h_meas_nonpos_g hs)
        ((measure_mono (set.inter_subset_right _ _)).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← measure.restrict_restrict (hm _ h_meas_nonpos_g),
      ← measure.restrict_restrict h_meas_nonpos_f],
    exact set_integral_nonpos_le (hm _ h_meas_nonpos_g) hf hfi, },
end

/-- Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫⁻ x in s, ‖g x‖₊ ∂μ ≤ ∫⁻ x in s, ‖f x‖₊ ∂μ` on all `m`-measurable sets with finite
measure. -/
lemma lintegral_nnnorm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ}
  (hf : strongly_measurable f) (hfi : integrable_on f s μ)
  (hg : strongly_measurable[m] g) (hgi : integrable_on g s μ)
  (hgf : ∀ t, measurable_set[m] t → μ t < ∞ → ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ)
  (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
  ∫⁻ x in s, ‖g x‖₊ ∂μ ≤ ∫⁻ x in s, ‖f x‖₊ ∂μ :=
begin
  rw [← of_real_integral_norm_eq_lintegral_nnnorm hfi,
    ← of_real_integral_norm_eq_lintegral_nnnorm hgi, ennreal.of_real_le_of_real_iff],
  { exact integral_norm_le_of_forall_fin_meas_integral_eq hm hf hfi hg hgi hgf hs hμs, },
  { exact integral_nonneg (λ x, norm_nonneg _), },
end

end integral_norm_le

end measure_theory
