import measure_theory.function.conditional_expectation
import probability.independence
import probability.notation

noncomputable theory
open topological_space measure_theory.Lp filter continuous_linear_map probability_theory
open_locale nnreal ennreal topological_space big_operators measure_theory probability_theory

namespace measure_theory

variables {α E : Type*} {m₁ m₂ m: measurable_space α}
  [normed_group E] [normed_space ℝ E]
  {μ : measure α} {f : α → E} [complete_space E]

lemma condexp_indep_eq
  (hle₁ : m₁ ≤ m) (hle₂ : m₂ ≤ m) [sigma_finite (μ.trim hle₂)]
  (hf : strongly_measurable[m₁] f) (hindp : indep m₁ m₂ μ) :
  μ[f | m₂] =ᵐ[μ] (λ x, μ[f]) :=
begin
  by_cases hfint : integrable f μ,
  swap, { exact (integral_undef hfint).symm ▸ condexp_undef hfint },
  have hfint₁ := hfint.trim hle₁ hf,
  refine (ae_eq_condexp_of_forall_set_integral_eq hle₂ hfint
    (λ s _ hs, integrable_on_const.2 (or.inr hs)) (λ s hms hs, _)
    strongly_measurable_const.ae_strongly_measurable').symm,
  rw set_integral_const,
  refine @integrable.induction _ _ m₁ _ _ _ _ _ _ _ f hfint₁,
  { intros c t hmt ht,
    rw [integral_indicator (hle₁ _ hmt), set_integral_const, smul_smul,
      ← ennreal.to_real_mul, mul_comm, ← hindp _ _ hmt hms, set_integral_indicator (hle₁ _ hmt),
      set_integral_const, set.inter_comm] },
  { intros u v hdisj huint hvint hu hv,
    have huint' := integrable_of_integrable_trim hle₁ huint,
    have hvint' := integrable_of_integrable_trim hle₁ hvint,
    rw [integral_add' huint' hvint', smul_add, hu, hv,
      integral_add' huint'.integrable_on hvint'.integrable_on] },
  { have heq₁ : (λ f : Lp E 1 (μ.trim hle₁), ∫ x, f x ∂μ) = λ f, ∫ x, f x ∂(μ.trim hle₁),
    { ext f,
      exact integral_trim _ (Lp.strongly_measurable _) },
    have heq₂ : (λ f : Lp E 1 (μ.trim hle₁), ∫ x in s, f x ∂μ) =
      (λ (f : Lp E 1 μ), ∫ x in s, f x ∂μ) ∘ (Lp_trim_clm μ hle₁),
    { ext f,
      exact integral_congr_ae ((ae_eq_restrict_iff_indicator_ae_eq (hle₂ _ hms)).2
        (eventually_eq.indicator (ae_eq_fun.coe_fn_mk _ _).symm)) },
    exact is_closed_eq
      (continuous.const_smul (heq₁.symm ▸ continuous_integral) _)
      (heq₂.symm ▸ (continuous_set_integral s).comp (continuous_linear_map.continuous _)) },
  { intros u v huv huint hueq,
    rwa [← integral_congr_ae (ae_eq_of_ae_eq_trim huv),
      ← (set_integral_congr_ae (hle₂ _ hms) _ : ∫ x in s, u x ∂μ = ∫ x in s, v x ∂μ)],
    filter_upwards [ae_eq_of_ae_eq_trim huv] with x hx _,
    exact hx }
end

end measure_theory
