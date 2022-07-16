/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.martingale.convergence
import probability.independence

open topological_space filter probability_theory
open_locale nnreal ennreal measure_theory probability_theory big_operators topological_space

namespace measure_theory

variables {α β ι : Type*} [preorder ι] {m m0 : measurable_space α} [measurable_space β]
  {μ : measure α} [is_finite_measure μ]

section PRed

variables {E : Type*} [normed_group E] [normed_space ℝ E]

section trim

/-- Given a measure `μ`, `Lp_trim_lm` is the linear map defined by the projection of the Lᵖ space
with respect to `μ` restricted on a sub-σ-algebra `m` to the original Lᵖ space. -/
noncomputable def Lp_trim_lm (p : ℝ≥0∞) (μ : measure α) (hle : m ≤ m0) :
  Lp E p (μ.trim hle) →ₗ[ℝ] Lp E p μ :=
{ to_fun := λ f, (mem_ℒp_of_mem_ℒp_trim hle (Lp.mem_ℒp f)).to_Lp f,
  map_add' := λ f g,
  begin
    rw ← mem_ℒp.to_Lp_add,
    exact mem_ℒp.to_Lp_congr _ _ (ae_eq_of_ae_eq_trim (Lp.coe_fn_add f g)),
  end,
  map_smul' := λ c f,
  begin
    rw ← mem_ℒp.to_Lp_const_smul,
    exact mem_ℒp.to_Lp_congr _ _ (ae_eq_of_ae_eq_trim (Lp.coe_fn_smul c f)),
  end }

/-- The projection of the L¹ space with respect to the measure `μ` restricted on a sub-σ-algebra `m`
to the original L¹ space is a continuous linear map. -/
noncomputable def L1_trim_clm (μ : measure α) (hle₁ : m ≤ m0) :
  Lp E 1 (μ.trim hle₁) →L[ℝ] Lp E 1 μ :=
linear_map.mk_continuous_of_exists_bound (Lp_trim_lm 1 μ hle₁)
begin
  refine ⟨1, λ x, le_of_eq _⟩,
  simp only [one_mul, Lp.norm_def, linear_map.coe_mk],
  rw [ennreal.to_real_eq_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _),
    snorm_trim hle₁ (Lp.strongly_measurable _)],
  exact snorm_congr_ae (ae_eq_fun.coe_fn_mk _ _),
end

end trim

variables [complete_space E] {m₁ m₂ m' : measurable_space α} {μ' : measure α} {f : α → E}

lemma set_integral_indicator {s t : set α} (ht : measurable_set t) :
  ∫ x in s, t.indicator f x ∂μ' = ∫ x in s ∩ t, f x ∂μ' :=
by rw [integral_indicator ht, measure.restrict_restrict ht, set.inter_comm]

/-- If `m₁, m₂` are independent σ-algebras and `f` is `m₁`-measurable, then `𝔼[f | m₂] = 𝔼[f]`
almost everywhere. -/
lemma condexp_indep_eq
  (hle₁ : m₁ ≤ m') (hle₂ : m₂ ≤ m') [sigma_finite (μ'.trim hle₂)]
  (hf : strongly_measurable[m₁] f) (hindp : indep m₁ m₂ μ') :
  μ'[f | m₂] =ᵐ[μ'] (λ x, ∫ x, f x ∂μ') :=
begin
  by_cases hfint : integrable f μ',
  swap, { exact (integral_undef hfint).symm ▸ condexp_undef hfint },
  have hfint₁ := hfint.trim hle₁ hf,
  refine (ae_eq_condexp_of_forall_set_integral_eq hle₂ hfint
    (λ s _ hs, integrable_on_const.2 (or.inr hs)) (λ s hms hs, _)
    strongly_measurable_const.ae_strongly_measurable').symm,
  rw set_integral_const,
  refine @integrable.induction _ _ m₁ _ _ _ _ _ _ _ f hfint₁,
  { intros c t hmt ht,
    rw [integral_indicator (hle₁ _ hmt), set_integral_const, smul_smul,
      ← ennreal.to_real_mul, mul_comm, ← hindp _ _ hmt hms,
      set_integral_indicator (hle₁ _ hmt),
      set_integral_const, set.inter_comm] },
  { intros u v hdisj huint hvint hu hv,
    have huint' := integrable_of_integrable_trim hle₁ huint,
    have hvint' := integrable_of_integrable_trim hle₁ hvint,
    rw [integral_add' huint' hvint', smul_add, hu, hv,
      integral_add' huint'.integrable_on hvint'.integrable_on] },
  { have heq₁ : (λ f : Lp E 1 (μ'.trim hle₁), ∫ x, f x ∂μ') = λ f, ∫ x, f x ∂(μ'.trim hle₁),
    { ext f,
      exact integral_trim _ (Lp.strongly_measurable _) },
    have heq₂ : (λ f : Lp E 1 (μ'.trim hle₁), ∫ x in s, f x ∂μ') =
      (λ f : Lp E 1 μ', ∫ x in s, f x ∂μ') ∘ (L1_trim_clm μ' hle₁),
    { ext f,
      exact integral_congr_ae ((ae_eq_restrict_iff_indicator_ae_eq (hle₂ _ hms)).2
        (eventually_eq.indicator (ae_eq_fun.coe_fn_mk _ _).symm)) },
    exact is_closed_eq
      (continuous.const_smul (heq₁.symm ▸ continuous_integral) _)
      (heq₂.symm ▸ (continuous_set_integral s).comp (continuous_linear_map.continuous _)) },
  { intros u v huv huint hueq,
    rwa [← integral_congr_ae (ae_eq_of_ae_eq_trim huv),
      ← (set_integral_congr_ae (hle₂ _ hms) _ : ∫ x in s, u x ∂μ' = ∫ x in s, v x ∂μ')],
    filter_upwards [ae_eq_of_ae_eq_trim huv] with x hx _,
    exact hx }
end

end PRed

section Levy

variables {ℱ : filtration ℕ m0}

/-- **Lévy's 0-1- law**, almost everywhere version: if `s` is a `⨆ n, ℱ n`-measurable set where
`ℱ` is a filtration, `ℙ(s | ℱ n)` converges to the indicator function of `s` almost everywhere. -/
lemma tendsto_ae_condexp_measurable_set {s : set α} (hs : measurable_set[⨆ n, ℱ n] s) :
  ∀ᵐ x ∂μ, tendsto (λ n, μ[s.indicator (λ x, 1 : α → ℝ) | ℱ n] x) at_top
    (𝓝 (s.indicator (λ x, 1 : α → ℝ) x)) :=
mem_ℒp.tendsto_ae_condexp (mem_ℒp_one_iff_integrable.2 $
  (integrable_indicator_iff ((supr_le $ λ n, ℱ.le n : (⨆ n, ℱ n) ≤ m0) _ hs)).2
  (integrable_on_const.2 (or.inr (measure_lt_top _ _))))
  (strongly_measurable_const.indicator hs)

/-- **Lévy's 0-1- law**, L¹ version: if `s` is a `⨆ n, ℱ n`-measurable set where `ℱ` is a
filtration, `ℙ(s | ℱ n)` converges to the indicator function of `s` in L¹. -/
lemma tendsto_snorm_condexp_measurable_set {s : set α} (hs : measurable_set[⨆ n, ℱ n] s) :
  tendsto (λ n, snorm (μ[s.indicator (λ x, 1 : α → ℝ) | ℱ n] - s.indicator (λ x, 1 : α → ℝ)) 1 μ)
    at_top (𝓝 0) :=
mem_ℒp.tendsto_snorm_condexp (mem_ℒp_one_iff_integrable.2 $
  (integrable_indicator_iff ((supr_le $ λ n, ℱ.le n : (⨆ n, ℱ n) ≤ m0) _ hs)).2
  (integrable_on_const.2 (or.inr (measure_lt_top _ _))))
  (strongly_measurable_const.indicator hs)

end Levy

section Kolmogorov

variables {E : Type*} [topological_space E] [metrizable_space E]
  [mE : measurable_space E] [borel_space E]

lemma indep_natural_tail {f : ι → α → E}
  (hf : ∀ i, strongly_measurable (f i)) (i : ι) (hindp : Indep_fun (λ x, mE) f μ) :
  indep (filtration.natural f hf i) (⨆ j > i, measurable_space.comap (f j) mE) μ :=
begin
  change indep (⨆ j ≤ i, measurable_space.comap (f j) mE)
    (⨆ j > i, measurable_space.comap (f j) mE) μ,
  rw Indep_fun at hindp,
  sorry
end

end Kolmogorov

end measure_theory
