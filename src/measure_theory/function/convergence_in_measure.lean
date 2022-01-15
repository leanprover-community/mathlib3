/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.function.uniform_integrable

/-!
# Convergence in measure

-/

open topological_space filter
open_locale nnreal ennreal measure_theory topological_space

namespace measure_theory

variables {α ι E : Type*} {m : measurable_space α} {μ : measure α}

/-- TODO -/
def tendsto_locally_in_measure [preorder ι] [has_dist E] {m : measurable_space α}
  (μ : measure α) (f : ι → α → E) (g : α → E) : Prop :=
∀ s (hs : measurable_set s) (hμs : 0 < μ s), ∀ ε (hε : 0 < ε),
  tendsto (λ i, μ {x ∈ s | ε ≤ dist (f i x) (g x)}) at_top (𝓝 0)

/-- TODO -/
def tendsto_in_measure [preorder ι] [has_dist E] {m : measurable_space α}
  (μ : measure α) (f : ι → α → E) (g : α → E) : Prop :=
∀ ε (hε : 0 < ε), tendsto (λ i, μ {x | ε ≤ dist (f i x) (g x)}) at_top (𝓝 0)

lemma tendsto_in_measure_iff_norm [preorder ι] [semi_normed_group E] {f : ι → α → E} {g : α → E} :
  tendsto_in_measure μ f g
    ↔ ∀ ε (hε : 0 < ε), tendsto (λ i, μ {x | ε ≤ ∥f i x - g x∥}) at_top (𝓝 0) :=
by simp_rw [tendsto_in_measure, dist_eq_norm]

namespace tendsto_in_measure

protected lemma tendsto_locally_in_measure [preorder ι] [has_dist E] {f : ι → α → E} {g : α → E}
  (h : tendsto_in_measure μ f g) :
  tendsto_locally_in_measure μ f g :=
begin
  intros s hs hμs ε hε,
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε) (λ i, zero_le _) _,
  exact λ i, measure_mono (λ x, by simp),
end

lemma congr_left [preorder ι] [has_dist E] {f f' : ι → α → E} {g : α → E}
  (h : ∀ i, f i =ᵐ[μ] f' i) (h_tendsto : tendsto_in_measure μ f g) :
  tendsto_in_measure μ f' g :=
begin
  intros ε hε,
  specialize h_tendsto ε hε,
  suffices : (λ i, μ {x | ε ≤ dist (f' i x) (g x)}) = (λ i, μ {x | ε ≤ dist (f i x) (g x)}),
    by rwa this,
  ext1 i,
  refine measure_congr ((h i).mono (λ x hx, _)),
  rw eq_iff_iff,
  change ε ≤ dist (f' i x) (g x) ↔ ε ≤ dist (f i x) (g x),
  rw hx,
end

lemma congr_right [preorder ι] [has_dist E] {f : ι → α → E} {g g' : α → E}
  (h : g =ᵐ[μ] g') (h_tendsto : tendsto_in_measure μ f g) :
  tendsto_in_measure μ f g' :=
begin
  intros ε hε,
  specialize h_tendsto ε hε,
  suffices : (λ i, μ {x | ε ≤ dist (f i x) (g' x)}) = (λ i, μ {x | ε ≤ dist (f i x) (g x)}),
    by rwa this,
  ext1 i,
  refine measure_congr (h.mono (λ x hx, _)),
  rw eq_iff_iff,
  change ε ≤ dist (f i x) (g' x) ↔ ε ≤ dist (f i x) (g x),
  rw hx,
end

variables [metric_space E] [second_countable_topology E] [measurable_space E] [borel_space E]
variables {f : ℕ → α → E} {g : α → E}

/-- Convergence a.e. implies convergence in measure in a finite measure space. -/
lemma of_tendsto_ae [is_finite_measure μ]
  (hf : ∀ n, measurable (f n)) (hg : measurable g)
  (hfg : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  tendsto_in_measure μ f g :=
begin
  refine λ ε hε, ennreal.tendsto_at_top_zero.mpr (λ δ hδ, _),
  by_cases hδi : δ = ∞,
  { simp only [hδi, implies_true_iff, le_top, exists_const], },
  lift δ to ℝ≥0 using hδi,
  rw [gt_iff_lt, ennreal.coe_pos, ← nnreal.coe_pos] at hδ,
  obtain ⟨t, htm, ht, hunif⟩ := tendsto_uniformly_on_of_ae_tendsto' hf hg hfg hδ,
  rw ennreal.of_real_coe_nnreal at ht,
  rw metric.tendsto_uniformly_on_iff at hunif,
  obtain ⟨N, hN⟩ := eventually_at_top.1 (hunif ε hε),
  refine ⟨N, λ n hn, _⟩,
  suffices : {x : α | ε ≤ dist (f n x) (g x)} ⊆ t, from (measure_mono this).trans ht,
  rw ← set.compl_subset_compl,
  intros x hx,
  rw [set.mem_compl_eq, set.nmem_set_of_eq, dist_comm, not_le],
  exact hN n hn x hx,
end

end tendsto_in_measure

end measure_theory
