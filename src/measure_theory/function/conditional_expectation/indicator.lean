/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.function.conditional_expectation.basic

/-!

# Conditional expectation of indicator functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves some results about the conditional expectation of an indicator function and
as a corollary, also proves several results about the behaviour of the conditional expectation on
a restricted measure.

## Main result

* `measure_theory.condexp_indicator`: If `s` is a `m`-measurable set, then the conditional
  expectation of the indicator function of `s` is almost everywhere equal to the indicator
  of `s` of the conditional expectation. Namely, `𝔼[s.indicator f | m] = s.indicator 𝔼[f | m]` a.e.

-/

noncomputable theory
open topological_space measure_theory.Lp filter continuous_linear_map
open_locale nnreal ennreal topology big_operators measure_theory

namespace measure_theory

variables {α 𝕜 E : Type*} {m m0 : measurable_space α}
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  {μ : measure α} {f : α → E} {s : set α}

lemma condexp_ae_eq_restrict_zero (hs : measurable_set[m] s) (hf : f =ᵐ[μ.restrict s] 0) :
  μ[f | m] =ᵐ[μ.restrict s] 0 :=
begin
  by_cases hm : m ≤ m0,
  swap, { simp_rw condexp_of_not_le hm, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { simp_rw condexp_of_not_sigma_finite hm hμm, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  haveI : sigma_finite ((μ.restrict s).trim hm),
  { rw ← restrict_trim hm _ hs,
    exact restrict.sigma_finite _ s, },
  by_cases hf_int : integrable f μ,
  swap, { rw condexp_undef hf_int, },
  refine ae_eq_of_forall_set_integral_eq_of_sigma_finite' hm _ _ _ _ _,
  { exact λ t ht hμt, integrable_condexp.integrable_on.integrable_on, },
  { exact λ t ht hμt, (integrable_zero _ _ _).integrable_on, },
  { intros t ht hμt,
    rw [measure.restrict_restrict (hm _ ht), set_integral_condexp hm hf_int (ht.inter hs),
      ← measure.restrict_restrict (hm _ ht)],
    refine set_integral_congr_ae (hm _ ht) _,
    filter_upwards [hf] with x hx h using hx, },
  { exact strongly_measurable_condexp.ae_strongly_measurable', },
  { exact strongly_measurable_zero.ae_strongly_measurable', },
end

/-- Auxiliary lemma for `condexp_indicator`. -/
lemma condexp_indicator_aux (hs : measurable_set[m] s) (hf : f =ᵐ[μ.restrict sᶜ] 0) :
  μ[s.indicator f | m] =ᵐ[μ] s.indicator (μ[f | m]) :=
begin
  by_cases hm : m ≤ m0,
  swap, { simp_rw [condexp_of_not_le hm, set.indicator_zero'], },
  have hsf_zero : ∀ g : α → E, g =ᵐ[μ.restrict sᶜ] 0 → s.indicator g =ᵐ[μ] g,
    from λ g, indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs),
  refine ((hsf_zero (μ[f | m]) (condexp_ae_eq_restrict_zero hs.compl hf)).trans _).symm,
  exact condexp_congr_ae (hsf_zero f hf).symm,
end

/-- The conditional expectation of the indicator of a function over an `m`-measurable set with
respect to the σ-algebra `m` is a.e. equal to the indicator of the conditional expectation. -/
lemma condexp_indicator (hf_int : integrable f μ) (hs : measurable_set[m] s) :
  μ[s.indicator f | m] =ᵐ[μ] s.indicator (μ[f | m]) :=
begin
  by_cases hm : m ≤ m0,
  swap, { simp_rw [condexp_of_not_le hm, set.indicator_zero'], },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { simp_rw [condexp_of_not_sigma_finite hm hμm, set.indicator_zero'], },
  haveI : sigma_finite (μ.trim hm) := hμm,
  -- use `have` to perform what should be the first calc step because of an error I don't
  -- understand
  have : s.indicator (μ[f|m]) =ᵐ[μ] s.indicator (μ[s.indicator f + sᶜ.indicator f|m]),
    by rw set.indicator_self_add_compl s f,
  refine (this.trans _).symm,
  calc s.indicator (μ[s.indicator f + sᶜ.indicator f|m])
      =ᵐ[μ] s.indicator (μ[s.indicator f|m] + μ[sᶜ.indicator f|m]) :
    begin
      have : μ[s.indicator f + sᶜ.indicator f|m] =ᵐ[μ] μ[s.indicator f|m] + μ[sᶜ.indicator f|m],
        from condexp_add (hf_int.indicator (hm _ hs)) (hf_int.indicator (hm _ hs.compl)),
      filter_upwards [this] with x hx,
      classical,
      rw [set.indicator_apply, set.indicator_apply, hx],
    end
  ... = s.indicator (μ[s.indicator f|m]) + s.indicator (μ[sᶜ.indicator f|m]) :
    s.indicator_add' _ _
  ... =ᵐ[μ] s.indicator (μ[s.indicator f|m]) + s.indicator (sᶜ.indicator (μ[sᶜ.indicator f|m])) :
    begin
      refine filter.eventually_eq.rfl.add _,
      have : sᶜ.indicator (μ[sᶜ.indicator f|m]) =ᵐ[μ] μ[sᶜ.indicator f|m],
      { refine (condexp_indicator_aux hs.compl _).symm.trans _,
        { exact indicator_ae_eq_restrict_compl (hm _ hs.compl), },
        { rw [set.indicator_indicator, set.inter_self], }, },
      filter_upwards [this] with x hx,
      by_cases hxs : x ∈ s,
      { simp only [hx, hxs, set.indicator_of_mem], },
      { simp only [hxs, set.indicator_of_not_mem, not_false_iff], },
    end
  ... =ᵐ[μ] s.indicator (μ[s.indicator f|m]) :
    by rw [set.indicator_indicator, set.inter_compl_self, set.indicator_empty', add_zero]
  ... =ᵐ[μ] μ[s.indicator f|m] :
    begin
      refine (condexp_indicator_aux hs _).symm.trans _,
      { exact indicator_ae_eq_restrict_compl (hm _ hs), },
      { rw [set.indicator_indicator, set.inter_self], },
    end
end

lemma condexp_restrict_ae_eq_restrict (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  (hs_m : measurable_set[m] s) (hf_int : integrable f μ) :
  (μ.restrict s)[f | m] =ᵐ[μ.restrict s] μ[f | m] :=
begin
  haveI : sigma_finite ((μ.restrict s).trim hm),
  { rw ← restrict_trim hm _ hs_m, apply_instance, },
  rw ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m),
  swap, { apply_instance, },
  refine eventually_eq.trans _ (condexp_indicator hf_int hs_m),
  refine ae_eq_condexp_of_forall_set_integral_eq hm (hf_int.indicator (hm _ hs_m)) _ _ _,
  { intros t ht hμt,
    rw [← integrable_indicator_iff (hm _ ht), set.indicator_indicator, set.inter_comm,
      ← set.indicator_indicator],
    suffices h_int_restrict : integrable (t.indicator ((μ.restrict s)[f|m])) (μ.restrict s),
    { rw [integrable_indicator_iff (hm _ hs_m), integrable_on],
      rw [integrable_indicator_iff (hm _ ht), integrable_on] at h_int_restrict ⊢,
      exact h_int_restrict, },
    exact integrable_condexp.indicator (hm _ ht), },
  { intros t ht hμt,
    calc ∫ x in t, s.indicator ((μ.restrict s)[f|m]) x ∂μ
        = ∫ x in t, ((μ.restrict s)[f|m]) x ∂(μ.restrict s) :
      by rw [integral_indicator (hm _ hs_m), measure.restrict_restrict (hm _ hs_m),
        measure.restrict_restrict (hm _ ht), set.inter_comm]
    ... = ∫ x in t, f x ∂(μ.restrict s) : set_integral_condexp hm hf_int.integrable_on ht
    ... = ∫ x in t, s.indicator f x ∂μ :
      by rw [integral_indicator (hm _ hs_m), measure.restrict_restrict (hm _ hs_m),
        measure.restrict_restrict (hm _ ht), set.inter_comm], },
  { exact (strongly_measurable_condexp.indicator hs_m).ae_strongly_measurable', },
end

/-- If the restriction to a `m`-measurable set `s` of a σ-algebra `m` is equal to the restriction
to `s` of another σ-algebra `m₂` (hypothesis `hs`), then `μ[f | m] =ᵐ[μ.restrict s] μ[f | m₂]`. -/
lemma condexp_ae_eq_restrict_of_measurable_space_eq_on {m m₂ m0 : measurable_space α}
  {μ : measure α} (hm : m ≤ m0) (hm₂ : m₂ ≤ m0)
  [sigma_finite (μ.trim hm)] [sigma_finite (μ.trim hm₂)]
  (hs_m : measurable_set[m] s) (hs : ∀ t, measurable_set[m] (s ∩ t) ↔ measurable_set[m₂] (s ∩ t)) :
  μ[f | m] =ᵐ[μ.restrict s] μ[f | m₂] :=
begin
  rw ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m),
  have hs_m₂ : measurable_set[m₂] s,
  { rwa [← set.inter_univ s, ← hs set.univ, set.inter_univ], },
  by_cases hf_int : integrable f μ,
  swap, { simp_rw condexp_undef hf_int, },
  refine ((condexp_indicator hf_int hs_m).symm.trans _).trans (condexp_indicator hf_int hs_m₂),
  refine ae_eq_of_forall_set_integral_eq_of_sigma_finite' hm₂
    (λ s hs hμs, integrable_condexp.integrable_on)
    (λ s hs hμs, integrable_condexp.integrable_on) _ _
    strongly_measurable_condexp.ae_strongly_measurable',
  swap,
  { have : strongly_measurable[m] (μ[s.indicator f | m]) := strongly_measurable_condexp,
    refine this.ae_strongly_measurable'.ae_strongly_measurable'_of_measurable_space_le_on
      hm hs_m (λ t, (hs t).mp) _,
    exact condexp_ae_eq_restrict_zero hs_m.compl (indicator_ae_eq_restrict_compl (hm _ hs_m)), },
  intros t ht hμt,
  have : ∫ x in t, μ[s.indicator f|m] x ∂μ = ∫ x in s ∩ t, μ[s.indicator f|m] x ∂μ,
  { rw ← integral_add_compl (hm _ hs_m) integrable_condexp.integrable_on,
    suffices : ∫ x in sᶜ, μ[s.indicator f|m] x ∂μ.restrict t = 0,
      by rw [this, add_zero, measure.restrict_restrict (hm _ hs_m)],
    rw measure.restrict_restrict (measurable_set.compl (hm _ hs_m)),
    suffices : μ[s.indicator f|m] =ᵐ[μ.restrict sᶜ] 0,
    { rw [set.inter_comm, ← measure.restrict_restrict (hm₂ _ ht)],
      calc ∫ (x : α) in t, μ[s.indicator f|m] x ∂μ.restrict sᶜ
          = ∫ (x : α) in t, 0 ∂μ.restrict sᶜ : begin
            refine set_integral_congr_ae (hm₂ _ ht) _,
            filter_upwards [this] with x hx h using hx,
          end
      ... = 0 : integral_zero _ _, },
    refine condexp_ae_eq_restrict_zero hs_m.compl _,
    exact indicator_ae_eq_restrict_compl (hm _ hs_m), },
  have hst_m : measurable_set[m] (s ∩ t) := (hs _).mpr (hs_m₂.inter ht),
  simp_rw [this, set_integral_condexp hm₂ (hf_int.indicator (hm _ hs_m)) ht,
    set_integral_condexp hm (hf_int.indicator (hm _ hs_m)) hst_m,
    integral_indicator (hm _ hs_m), measure.restrict_restrict (hm _ hs_m),
    ← set.inter_assoc, set.inter_self],
end

end measure_theory
