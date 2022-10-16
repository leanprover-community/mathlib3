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

open measure_theory probability_theory measurable_space

namespace probability_theory

variables {Ω : Type*} {m0 : measurable_space Ω} {μ : measure Ω} {s : ℕ → set Ω}

section pi_system

lemma Indep_set.indep_generate_from_le [is_probability_measure μ]
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (n : ℕ) :
  indep (generate_from {s (n + 1)}) (generate_from {t | ∃ k ≤ n, s k = t}) μ :=
begin
  have := hs.indep_generate_from_of_disjoint _ hsm {n + 1} {k | k ≤ n} (λ x ⟨hx₁, hx₂⟩,
    not_lt.2 (set.mem_set_of.1 hx₂) ((set.mem_singleton_iff.1 hx₁).symm ▸ nat.lt_succ_self n)),
  convert this,
  simp only [set.mem_singleton_iff, exists_prop, exists_eq_left, set.set_of_eq_eq_singleton'],
end

end pi_system

section borel_cantelli

/-- Given a sequence of measurable sets `(sₙ)`, `filtration_of_set` is the smallest filtration
such that `sₙ` is measurable with respect to the `n`-the sub-σ-algebra in `filtration_of_set`. -/
def filtration_of_set {s : ℕ → set Ω} (hsm : ∀ n, measurable_set (s n)) : filtration ℕ m0 :=
{ seq := λ n, generate_from {t | ∃ k ≤ n, s k = t},
  mono' := λ n m hnm, generate_from_mono (λ t ⟨k, hk₁, hk₂⟩, ⟨k, hk₁.trans hnm, hk₂⟩),
  le' := λ n, generate_from_le (λ t ⟨k, hk₁, hk₂⟩, hk₂ ▸ hsm k) }

lemma measurable_set_filtration_of_set {s : ℕ → set Ω}
  (hsm : ∀ n, measurable_set[m0] (s n)) (n : ℕ) {k : ℕ} (hk : k ≤ n) :
  measurable_set[filtration_of_set hsm n] (s k) :=
measurable_set_generate_from ⟨k, hk, rfl⟩

lemma measurable_set_filtration_of_set' {s : ℕ → set Ω}
  (hsm : ∀ n, measurable_set[m0] (s n)) (n : ℕ) :
  measurable_set[filtration_of_set hsm n] (s n) :=
measurable_set_filtration_of_set hsm n le_rfl

variables [is_probability_measure μ]

lemma Indep_set.filtration_of_set_indep
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (n : ℕ) :
  indep (generate_from {s (n + 1)}) (filtration_of_set hsm n) μ :=
hs.indep_generate_from_le hsm _

lemma Indep_set.condexp_indicator_filtration_of_set_ae_eq
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (n : ℕ) :
  μ[(s (n + 1)).indicator (λ ω, 1 : Ω → ℝ) | filtration_of_set hsm n] =ᵐ[μ]
    λ ω, (μ (s (n + 1))).to_real :=
begin
  refine (condexp_indep_eq (generate_from_le
    (λ t ht, (set.mem_singleton_iff.1 ht).symm ▸ hsm _) : generate_from {s (n + 1)} ≤ m0)
    ((filtration_of_set hsm).le n)
    (strongly_measurable_one.indicator (measurable_set_generate_from (set.mem_singleton _)))
    (hs.indep_generate_from_le hsm n)).trans (ae_of_all μ (λ ω, _)),
  convert integral_indicator_const (1 : ℝ) (hsm (n + 1)),
  rw [smul_eq_mul, mul_one],
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
