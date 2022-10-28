/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.martingale.borel_cantelli
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

open_locale measure_theory probability_theory ennreal big_operators topological_space

open measure_theory probability_theory measurable_space topological_space

namespace probability_theory

variables {Ω : Type*} {m0 : measurable_space Ω} {μ : measure Ω} {s : ℕ → set Ω}

section borel_cantelli

section move

variables {β : Type*} [mβ : measurable_space β]

lemma measurable.comap_le_of_measurable {f : Ω → β} (hf : measurable f) :
  mβ.comap f ≤ m0 :=
begin
  rintro s ⟨t, ht, rfl⟩,
  exact hf ht
end

lemma measurable_space.comap_measurable (f : Ω → β) :
  measurable[mβ.comap f] f :=
λ s hs, ⟨s, hs, rfl⟩

variables [normed_add_comm_group β] [borel_space β]

variables [is_probability_measure μ]

lemma Indep_fun.indep_comap_succ_natural {f : ℕ → Ω → β}
  (hf : ∀ (i : ℕ), strongly_measurable (f i))
  (hfi : Indep_fun (λ (n : ℕ), mβ) f μ) (n : ℕ) :
  indep (measurable_space.comap (f (n + 1)) mβ) (filtration.natural f hf n) μ :=
begin
  suffices : indep (⨆ k ∈ {n + 1}, measurable_space.comap (f k) mβ)
    (⨆ k ∈ {k | k ≤ n}, measurable_space.comap (f k) mβ) μ,
  { rwa supr_singleton at this },
  refine indep_supr_of_disjoint (λ k, (hf k).measurable.comap_le_of_measurable) hfi _,
  simp
end

lemma Indep_fun.condexp_succ_natrual_ae_eq
  [second_countable_topology β] [complete_space β] [normed_space ℝ β]
  {f : ℕ → Ω → β} (hf : ∀ i, strongly_measurable (f i)) (hfi : Indep_fun (λ n, mβ) f μ) (n : ℕ) :
  μ[f (n + 1) | filtration.natural f hf n] =ᵐ[μ] λ ω, μ[f (n + 1)] :=
condexp_indep_eq (hf $ n + 1).measurable.comap_le_of_measurable
  (filtration.le _ _) (measurable_space.comap_measurable $ f $ n + 1).strongly_measurable
  (hfi.indep_comap_succ_natural hf n)

end move

lemma Indep_set.Indep_fun_indicator (hs : Indep_set s μ) :
  Indep_fun (λ n, real.measurable_space) (λ n, (s n).indicator (λ ω, 1)) μ :=
begin
  classical,
  rw Indep_fun_iff_measure_inter_preimage_eq_mul,
  rintro S π hπ,
  simp_rw set.indicator_const_preimage_eq_union,
  refine @hs S (λ i, ite (1 ∈ π i) (s i) ∅ ∪ ite ((0 : ℝ) ∈ π i) (s i)ᶜ ∅) _,
  rintros i hi,
  simp only [set.mem_set_of],
  split_ifs,
  { simp only [set.union_compl_self, measurable_set.univ] },
  { rw set.union_empty,
    exact measurable_set_generate_from (set.mem_singleton _) },
  { rw set.empty_union,
    exact (measurable_set_generate_from (set.mem_singleton _)).compl },
  { simp only [set.empty_union, measurable_set.empty] }
end

variables [is_probability_measure μ]

lemma Indep_set.condexp_indicator_filtration_of_set_ae_eq
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (n : ℕ) :
  μ[(s (n + 1)).indicator (λ ω, 1 : Ω → ℝ) | filtration_of_set hsm n] =ᵐ[μ]
    λ ω, (μ (s (n + 1))).to_real :=
begin
  rw filtration.filtration_of_set_eq_natural hsm,
  refine (Indep_fun.condexp_succ_natrual_ae_eq _ hs.Indep_fun_indicator n).trans _,
  simp only [integral_indicator_const _ (hsm _), algebra.id.smul_eq_mul, mul_one],
end

lemma Indep_set.condexp_indicator_filtration_of_set_ae_eq'
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) :
  ∀ᵐ ω ∂μ, ∀ n, μ[(s (n + 1)).indicator (1 : Ω → ℝ) | filtration_of_set hsm n] ω =
    (μ (s (n + 1))).to_real :=
ae_all_iff.2 (hs.condexp_indicator_filtration_of_set_ae_eq hsm)

open filter

/-- **The second Borel-Cantelli lemma**: Given a sequence of independent sets `(sₙ)` such that
`∑ n, μ sₙ = ∞`, `limsup sₙ` has measure 1. -/
lemma measure_limsup_eq_one
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
  filter_upwards [hs.condexp_indicator_filtration_of_set_ae_eq' hsm] with ω hω,
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
    refine not_eventually.2 _ (htends B.to_nnreal),
    refine frequently_of_forall (λ n, not_lt.2 _),
    rw mem_upper_bounds at hB,
    specialize hB (∑ (k : ℕ) in finset.range n, μ (s (k + 1))).to_real _,
    { refine ⟨n, _⟩,
      rw ennreal.to_real_sum,
      exact λ _ _, measure_ne_top _ _ },
    { rw ← ennreal.to_real_le_to_real (ennreal.sum_lt_top _).ne ennreal.coe_ne_top,
      { exact hB.trans (by simp) },
      { exact λ _ _, measure_ne_top _ _ } } }
end

end borel_cantelli

end probability_theory
