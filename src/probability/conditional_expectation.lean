/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.notation
import probability.independence
import measure_theory.function.conditional_expectation.basic

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

variables {Ω E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  {m₁ m₂ m : measurable_space Ω} {μ : measure Ω} {f : Ω → E}

/-- If `m₁, m₂` are independent σ-algebras and `f` is `m₁`-measurable, then `𝔼[f | m₂] = 𝔼[f]`
almost everywhere. -/
lemma condexp_indep_eq
  (hle₁ : m₁ ≤ m) (hle₂ : m₂ ≤ m) [sigma_finite (μ.trim hle₂)]
  (hf : strongly_measurable[m₁] f) (hindp : indep m₁ m₂ μ) :
  μ[f | m₂] =ᵐ[μ] λ x, μ[f] :=
begin
  by_cases hfint : integrable f μ,
  swap, { rw [condexp_undef hfint, integral_undef hfint], refl, },
  have hfint₁ := hfint.trim hle₁ hf,
  refine (ae_eq_condexp_of_forall_set_integral_eq hle₂ hfint
    (λ s _ hs, integrable_on_const.2 (or.inr hs)) (λ s hms hs, _)
    strongly_measurable_const.ae_strongly_measurable').symm,
  rw set_integral_const,
  rw ← mem_ℒp_one_iff_integrable at hfint,
  refine hfint.induction_strongly_measurable hle₁ ennreal.one_ne_top _ _ _ _ _ _,
  { intros c t hmt ht,
    rw [integral_indicator (hle₁ _ hmt), set_integral_const, smul_smul,
      ← ennreal.to_real_mul, mul_comm, ← hindp _ _ hmt hms, set_integral_indicator (hle₁ _ hmt),
      set_integral_const, set.inter_comm] },
  { intros u v hdisj huint hvint hu hv hu_eq hv_eq,
    rw mem_ℒp_one_iff_integrable at huint hvint,
    rw [integral_add' huint hvint, smul_add, hu_eq, hv_eq,
      integral_add' huint.integrable_on hvint.integrable_on], },
  { have heq₁ : (λ f : Lp_meas E ℝ m₁ 1 μ, ∫ x, f x ∂μ) =
      (λ f : Lp E 1 μ, ∫ x, f x ∂μ) ∘ (submodule.subtypeL _),
    { refine funext (λ f, integral_congr_ae _),
      simp_rw [submodule.coe_subtypeL', submodule.coe_subtype, ← coe_fn_coe_base], },
    have heq₂ : (λ f : Lp_meas E ℝ m₁ 1 μ, ∫ x in s, f x ∂μ) =
      (λ f : Lp E 1 μ, ∫ x in s, f x ∂μ) ∘ (submodule.subtypeL _),
    { refine funext (λ f, integral_congr_ae (ae_restrict_of_ae _)),
      simp_rw [submodule.coe_subtypeL', submodule.coe_subtype, ← coe_fn_coe_base],
      exact eventually_of_forall (λ _, rfl), },
    refine is_closed_eq (continuous.const_smul _ _) _,
    { rw heq₁,
      exact continuous_integral.comp (continuous_linear_map.continuous _), },
    { rw heq₂,
      exact (continuous_set_integral _).comp (continuous_linear_map.continuous _), }, },
  { intros u v huv huint hueq,
    rwa [← integral_congr_ae huv,
      ← (set_integral_congr_ae (hle₂ _ hms) _ : ∫ x in s, u x ∂μ = ∫ x in s, v x ∂μ)],
    filter_upwards [huv] with x hx _ using hx, },
  { exact ⟨f, hf, eventually_eq.rfl⟩, },
end

end measure_theory
