/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.notation
import probability.independence

/-!

# Probabilistic properties of the conditional expectation

This file contains some properties about the conditional expectation which does not belong in
the main conditional expectation file.

## Main result

* `measure_theory.condexp_indep_eq`: If `m₁, m₂` are independent σ-algebras and `f` is a
  `m₁`-measurable function, then `𝔼[f | m₂] = 𝔼[f]` almost everywhere.

-/

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators

namespace measure_theory

open probability_theory

variables {α E : Type*} [normed_group E] [normed_space ℝ E] [complete_space E]
  {m₁ m₂ m : measurable_space α} {μ : measure α} {f : α → E}

/-- If `m₁, m₂` are independent σ-algebras and `f` is `m₁`-measurable, then `𝔼[f | m₂] = 𝔼[f]`
almost everywhere. -/
lemma condexp_indep_eq
  (hle₁ : m₁ ≤ m) (hle₂ : m₂ ≤ m) [sigma_finite (μ.trim hle₂)]
  (hf : strongly_measurable[m₁] f) (hindp : indep m₁ m₂ μ) :
  μ[f | m₂] =ᵐ[μ] λ x, μ[f] :=
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
      (λ f : Lp E 1 μ, ∫ x in s, f x ∂μ) ∘ (L1_trim_clm μ hle₁),
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
