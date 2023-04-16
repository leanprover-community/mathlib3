/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.martingale.borel_cantelli
import probability.conditional_expectation
import probability.independence

/-!

# The second Borel-Cantelli lemma

This file contains the second Borel-Cantelli lemma which states that, given a sequence of
independent sets `(sₙ)` in a probability space, if `∑ n, μ sₙ = ∞`, then the limsup of `sₙ` has
measure 1. We employ a proof using Lévy's generalized Borel-Cantelli by choosing an appropriate
filtration.

## Main result

- `probability_theory.measure_limsup_eq_one`: the second Borel-Cantelli lemma.

-/

open_locale measure_theory probability_theory ennreal big_operators topology

open measure_theory probability_theory measurable_space topological_space

namespace probability_theory

variables {Ω : Type*} {m0 : measurable_space Ω} {μ : measure Ω}
  [is_probability_measure μ]

section borel_cantelli

variables {ι β : Type*} [linear_order ι] [mβ : measurable_space β] [normed_add_comm_group β]
  [borel_space β] {f : ι → Ω → β} {i j : ι} {s : ι → set Ω}

lemma Indep_fun.indep_comap_natural_of_lt (hf : ∀ i, strongly_measurable (f i))
  (hfi : Indep_fun (λ i, mβ) f μ) (hij : i < j) :
  indep (measurable_space.comap (f j) mβ) (filtration.natural f hf i) μ :=
begin
  suffices : indep (⨆ k ∈ {j}, measurable_space.comap (f k) mβ)
    (⨆ k ∈ {k | k ≤ i}, measurable_space.comap (f k) mβ) μ,
  { rwa supr_singleton at this },
  exact indep_supr_of_disjoint (λ k, (hf k).measurable.comap_le) hfi (by simpa),
end

lemma Indep_fun.condexp_natrual_ae_eq_of_lt
  [second_countable_topology β] [complete_space β] [normed_space ℝ β]
  (hf : ∀ i, strongly_measurable (f i)) (hfi : Indep_fun (λ i, mβ) f μ) (hij : i < j) :
  μ[f j | filtration.natural f hf i] =ᵐ[μ] λ ω, μ[f j] :=
condexp_indep_eq (hf j).measurable.comap_le (filtration.le _ _)
  (comap_measurable $ f j).strongly_measurable
  (hfi.indep_comap_natural_of_lt hf hij)

lemma Indep_set.condexp_indicator_filtration_of_set_ae_eq
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (hij : i < j) :
  μ[(s j).indicator (λ ω, 1 : Ω → ℝ) | filtration_of_set hsm i] =ᵐ[μ] λ ω, (μ (s j)).to_real :=
begin
  rw filtration.filtration_of_set_eq_natural hsm,
  refine (Indep_fun.condexp_natrual_ae_eq_of_lt _ hs.Indep_fun_indicator hij).trans _,
  { simp only [integral_indicator_const _ (hsm _), algebra.id.smul_eq_mul, mul_one] },
  { apply_instance }
end

open filter

/-- **The second Borel-Cantelli lemma**: Given a sequence of independent sets `(sₙ)` such that
`∑ n, μ sₙ = ∞`, `limsup sₙ` has measure 1. -/
lemma measure_limsup_eq_one {s : ℕ → set Ω}
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (hs' : ∑' n, μ (s n) = ∞) :
  μ (limsup s at_top) = 1 :=
begin
  rw measure_congr (eventually_eq_set.2 (ae_mem_limsup_at_top_iff μ $
    measurable_set_filtration_of_set' hsm) :
      (limsup s at_top : set Ω) =ᵐ[μ] {ω | tendsto (λ n, ∑ k in finset.range n,
        μ[(s (k + 1)).indicator (1 : Ω → ℝ) | filtration_of_set hsm k] ω) at_top at_top}),
  suffices : {ω | tendsto (λ n, ∑ k in finset.range n,
    μ[(s (k + 1)).indicator (1 : Ω → ℝ) | filtration_of_set hsm k] ω) at_top at_top} =ᵐ[μ] set.univ,
  { rw [measure_congr this, measure_univ] },
  have : ∀ᵐ ω ∂μ, ∀ n, μ[(s (n + 1)).indicator (1 : Ω → ℝ) | filtration_of_set hsm n] ω = _ :=
    ae_all_iff.2 (λ n, hs.condexp_indicator_filtration_of_set_ae_eq hsm n.lt_succ_self),
  filter_upwards [this] with ω hω,
  refine eq_true_intro (_ : tendsto _ _ _),
  simp_rw hω,
  have htends : tendsto (λ n, ∑ k in finset.range n, μ (s (k + 1))) at_top (𝓝 ∞),
  { rw ← ennreal.tsum_add_one_eq_top hs' (measure_ne_top _ _),
    exact ennreal.tendsto_nat_tsum _ },
  rw ennreal.tendsto_nhds_top_iff_nnreal at htends,
  refine tendsto_at_top_at_top_of_monotone' _ _,
  { refine monotone_nat_of_le_succ (λ n, _),
    rw [← sub_nonneg, finset.sum_range_succ_sub_sum],
    exact ennreal.to_real_nonneg },
  { rintro ⟨B, hB⟩,
    refine not_eventually.2 (frequently_of_forall $ λ n, _) (htends B.to_nnreal),
    rw mem_upper_bounds at hB,
    specialize hB (∑ (k : ℕ) in finset.range n, μ (s (k + 1))).to_real _,
    { refine ⟨n, _⟩,
      rw ennreal.to_real_sum,
      exact λ _ _, measure_ne_top _ _ },
    { rw [not_lt, ← ennreal.to_real_le_to_real (ennreal.sum_lt_top _).ne ennreal.coe_ne_top],
      { exact hB.trans (by simp) },
      { exact λ _ _, measure_ne_top _ _ } } }
end

end borel_cantelli

end probability_theory
