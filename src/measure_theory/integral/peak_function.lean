/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.group.integration
import measure_theory.group.prod
import measure_theory.function.locally_integrable


/-!
# Integrals against peak functions

A sequence of peak functions is a sequence of functions with average one concentrating around
a point `x₀`. Given such a sequence `φₙ`, then `∫ φₙ g` tends to `g x₀` in many situations, with
a whole zoo of possible assumptions on `φₙ` and `g`. This file is devoted to such results.

## Main results

* `tendsto_set_integral_peak_smul_of_integrable_on_of_continuous_within_at`: If a sequence of peak
  functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
  `g` is integrable and continuous at `x₀`, then `∫ φᵢ • g` converges to `x₀`.

-/

open set function filter measure_theory measure_theory.measure topological_space metric
open_locale topological_space nnreal filter ennreal

/-- This lemma exists for finsets, but not for sets currently. porting note: move to
data.set.basic after the port. -/
lemma set.disjoint_sdiff_inter {α : Type*} (s t : set α) : disjoint (s \ t) (s ∩ t) :=
disjoint_of_subset_right (inter_subset_right _ _) disjoint_sdiff_left

open set

variables {G E ι : Type*} {hm : measurable_space G} {μ : measure G}
  [topological_space G] [borel_space G]
  [normed_add_comm_group E] [normed_space ℝ E]
  {g : G → E} {l : filter ι} {x₀ : G} {s : set G} {φ : ι → G → ℝ}

/-- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
`g` is integrable and continuous at `x₀`, then `φᵢ • g` is eventually integrable. -/
lemma integrable_on_peak_smul_of_integrable_on_of_continuous_within_at
  (hs : measurable_set s)
  (hlφ : ∀ (u : set G), is_open u → x₀ ∈ u → tendsto_uniformly_on φ 0 l (s \ u))
  (hiφ : ∀ᶠ i in l, ∫ x in s, φ i x ∂μ = 1)
  (hmg : integrable_on g s μ)
  (hcg : continuous_within_at g s x₀) :
  ∀ᶠ i in l, integrable_on (λ x, φ i x • g x) s μ :=
begin
  obtain ⟨u, u_open, x₀u, hu⟩ : ∃ u, is_open u ∧ x₀ ∈ u ∧ ∀ x ∈ u ∩ s, g x ∈ ball (g x₀) 1,
    from mem_nhds_within.1 (hcg (ball_mem_nhds _ zero_lt_one)),
  filter_upwards [tendsto_uniformly_on_iff.1 (hlφ u u_open x₀u) 1 zero_lt_one, hiφ]
    with i hi h'i,
  have A : integrable_on (λ x, φ i x • g x) (s \ u) μ,
  { apply integrable.smul_of_top_right (hmg.mono (diff_subset _ _) le_rfl),
    apply mem_ℒp_top_of_bound
      ((integrable_of_integral_eq_one h'i).ae_strongly_measurable.mono_set ((diff_subset _ _))) 1,
    filter_upwards [self_mem_ae_restrict (hs.diff u_open.measurable_set)] with x hx,
    simpa only [pi.zero_apply, dist_zero_left] using (hi x hx).le },
  have B : integrable_on (λ x, φ i x • g x) (s ∩ u) μ,
  { apply integrable.smul_of_top_left,
    { exact integrable_on.mono_set (integrable_of_integral_eq_one h'i) (inter_subset_left _ _) },
    { apply mem_ℒp_top_of_bound (hmg.mono_set (inter_subset_left _ _)).ae_strongly_measurable
        (‖g x₀‖ + 1),
      filter_upwards [self_mem_ae_restrict (hs.inter u_open.measurable_set)] with x hx,
      rw inter_comm at hx,
      exact (norm_lt_of_mem_ball (hu x hx)).le } },
  convert A.union B,
  simp only [diff_union_inter],
end

variables [complete_space E]

/-- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
`g` is integrable and continuous at `x₀`, then `∫ φᵢ • g` converges to `x₀`. Auxiliary lemma
where one assumes additionally `g x₀ = 0`. -/
lemma tendsto_set_integral_peak_smul_of_integrable_on_of_continuous_within_at_aux
  (hs : measurable_set s)
  (hnφ : ∀ᶠ i in l, ∀ x ∈ s, 0 ≤ φ i x)
  (hlφ : ∀ (u : set G), is_open u → x₀ ∈ u → tendsto_uniformly_on φ 0 l (s \ u))
  (hiφ : ∀ᶠ i in l, ∫ x in s, φ i x ∂μ = 1)
  (hmg : integrable_on g s μ) (h'g : g x₀ = 0)
  (hcg : continuous_within_at g s x₀) :
  tendsto (λ i : ι, ∫ x in s, φ i x • g x ∂μ) l (𝓝 0) :=
begin
  refine metric.tendsto_nhds.2 (λ ε εpos, _),
  obtain ⟨δ, hδ, δpos⟩ : ∃ δ, δ * ∫ x in s, ‖g x‖ ∂μ + δ < ε ∧ 0 < δ,
  { have A : tendsto (λ δ, δ * ∫ x in s, ‖g x‖ ∂μ + δ) (𝓝[>] 0) (𝓝 (0 * ∫ x in s, ‖g x‖ ∂μ + 0)),
    { apply tendsto.mono_left _ nhds_within_le_nhds,
      exact (tendsto_id.mul tendsto_const_nhds).add tendsto_id },
    rw [zero_mul, zero_add] at A,
    exact (((tendsto_order.1 A).2 ε εpos).and self_mem_nhds_within).exists },
  suffices : ∀ᶠ i in l, ‖∫ x in s, φ i x • g x ∂μ‖ ≤ δ * ∫ x in s, ‖g x‖ ∂μ + δ,
  { filter_upwards [this] with i hi,
    simp only [dist_zero_right],
    exact hi.trans_lt hδ },
  obtain ⟨u, u_open, x₀u, hu⟩ : ∃ u, is_open u ∧ x₀ ∈ u ∧ ∀ x ∈ u ∩ s, g x ∈ ball (g x₀) δ,
    from mem_nhds_within.1 (hcg (ball_mem_nhds _ δpos)),
  filter_upwards [tendsto_uniformly_on_iff.1 (hlφ u u_open x₀u) δ δpos, hiφ, hnφ,
    integrable_on_peak_smul_of_integrable_on_of_continuous_within_at hs hlφ hiφ hmg hcg]
      with i hi h'i hφpos h''i,
  have B : ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ ≤ δ, from calc
    ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ ≤ ∫ x in s ∩ u, ‖φ i x • g x‖ ∂μ :
      norm_integral_le_integral_norm _
    ... ≤ ∫ x in s ∩ u, ‖φ i x‖ * δ ∂μ :
      begin
        refine set_integral_mono_on _ _ (hs.inter u_open.measurable_set) (λ x hx, _),
        { exact integrable_on.mono_set h''i.norm (inter_subset_left _ _) },
        { exact integrable_on.mono_set ((integrable_of_integral_eq_one h'i).norm.mul_const _)
            (inter_subset_left _ _) },
        rw norm_smul,
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
        rw [inter_comm, h'g] at hu,
        exact (mem_ball_zero_iff.1 (hu x hx)).le,
      end
    ... ≤ ∫ x in s, ‖φ i x‖ * δ ∂μ :
      begin
        apply set_integral_mono_set,
        { exact ((integrable_of_integral_eq_one h'i).norm.mul_const _) },
        { exact eventually_of_forall (λ x, mul_nonneg (norm_nonneg _) δpos.le) },
        { apply eventually_of_forall, exact inter_subset_left s u }
      end
    ... = ∫ x in s, φ i x * δ ∂μ :
      begin
        apply set_integral_congr hs (λ x hx, _),
        rw real.norm_of_nonneg (hφpos _ hx),
      end
    ... = δ : by rw [integral_mul_right, h'i, one_mul],
  have C : ‖∫ x in s \ u, φ i x • g x ∂μ‖ ≤ δ * ∫ x in s, ‖g x‖ ∂μ, from calc
    ‖∫ x in s \ u, φ i x • g x ∂μ‖ ≤ ∫ x in s \ u, ‖φ i x • g x‖ ∂μ :
      norm_integral_le_integral_norm _
    ... ≤ ∫ x in s \ u, δ * ‖g x‖ ∂μ :
      begin
        refine set_integral_mono_on _ _ (hs.diff u_open.measurable_set) (λ x hx, _),
        { exact integrable_on.mono_set h''i.norm (diff_subset _ _) },
        { exact integrable_on.mono_set (hmg.norm.const_mul _) (diff_subset _ _) },
        rw norm_smul,
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
        simpa only [pi.zero_apply, dist_zero_left] using (hi x hx).le,
      end
    ... ≤ δ * ∫ x in s, ‖g x‖ ∂μ :
      begin
        rw integral_mul_left,
        apply mul_le_mul_of_nonneg_left (set_integral_mono_set hmg.norm _ _) δpos.le,
        { exact eventually_of_forall (λ x, norm_nonneg _) },
        { apply eventually_of_forall, exact diff_subset s u }
      end,
  calc
  ‖∫ x in s, φ i x • g x ∂μ‖ = ‖∫ x in s \ u, φ i x • g x ∂μ + ∫ x in s ∩ u, φ i x • g x ∂μ‖ :
    begin
      conv_lhs { rw ← diff_union_inter s u },
      rw integral_union (disjoint_sdiff_inter _ _) (hs.inter u_open.measurable_set)
        (h''i.mono_set (diff_subset _ _)) (h''i.mono_set (inter_subset_left _ _))
    end
  ... ≤ ‖∫ x in s \ u, φ i x • g x ∂μ‖ + ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ : norm_add_le _ _
  ... ≤ δ * ∫ x in s, ‖g x‖ ∂μ + δ : add_le_add C B
end

/- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
`g` is integrable and continuous at `x₀`, then `∫ φᵢ • g` converges to `x₀`. -/
lemma tendsto_set_integral_peak_smul_of_integrable_on_of_continuous_within_at
  (hs : measurable_set s) (h's : μ s < ∞)
  (hnφ : ∀ᶠ i in l, ∀ x ∈ s, 0 ≤ φ i x)
  (hlφ : ∀ (u : set G), is_open u → x₀ ∈ u → tendsto_uniformly_on φ 0 l (s \ u))
  (hiφ : (λ i, ∫ x in s, φ i x ∂μ) =ᶠ[l] 1)
  (hmg : integrable_on g s μ)
  (hcg : continuous_within_at g s x₀) :
  tendsto (λ i : ι, ∫ x in s, φ i x • g x ∂μ) l (𝓝 (g x₀)) :=
begin
  let h := g - (λ y, g x₀),
  have A : tendsto (λ i : ι, ∫ x in s, φ i x • h x ∂μ + (∫ x in s, φ i x ∂μ) • g x₀) l
    (𝓝 (0 + (1 : ℝ) • g x₀)),
  { refine tendsto.add _ (tendsto.smul (tendsto_const_nhds.congr' hiφ.symm) tendsto_const_nhds),
    apply tendsto_set_integral_peak_smul_of_integrable_on_of_continuous_within_at_aux
      hs hnφ hlφ hiφ,
    { apply integrable.sub hmg,
      apply integrable_on_const.2,
      simp only [h's, or_true] },
    { simp only [h, pi.sub_apply, sub_self] },
    { exact hcg.sub continuous_within_at_const } },
  simp only [one_smul, zero_add] at A,
  refine tendsto.congr' _ A,
  filter_upwards [integrable_on_peak_smul_of_integrable_on_of_continuous_within_at
    hs hlφ hiφ hmg hcg, hiφ] with i hi h'i,
  simp only [h, pi.sub_apply, smul_sub],
  rw [integral_sub hi, integral_smul_const, sub_add_cancel],
  exact integrable.smul_const (integrable_of_integral_eq_one h'i) _,
end
