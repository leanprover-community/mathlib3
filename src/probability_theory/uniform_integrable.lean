/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/

import measure_theory.integral.set_integral

-- Probability should move to `measure_theory/integral`

noncomputable theory
open_locale classical measure_theory nnreal ennreal topological_space

namespace measure_theory

open set filter topological_space

section move

/-
### Egorov's theorem

If `f : ℕ → α → β` is a sequence of measurable functions where `β` is a separable metric space,
and `f` converges to `g : α → β` almost surely on a measurable set `s : set α` of finite measure,
then, for all `ε > 0`, there exists a subset `t ⊆ s` such that `μ t < ε` and `f` converges to
`g` uniformly on `A \ B`.

Useful:
-- `nnreal.has_sum_geometric` in `analysis.specific_limits`
-/

variables {α β ι : Type*} {m : measurable_space α}
  [metric_space β] [second_countable_topology β] [measurable_space β] [borel_space β]
  {μ : measure α}

private def antitoneseq (f : ℕ → α → β) (g : α → β) (ε : ℝ≥0∞) (i j : ℕ) : set α :=
⋃ k (hk : j ≤ k), {x | 2^(-(i : ℤ)) < dist (f k x) (g x)}

variables {f : ℕ → α → β} {g : α → β} {ε : ℝ≥0∞}

private lemma antitoneseq_measurable_set
  (hf : ∀ n, measurable[m] (f n)) (hg : measurable g)
  {i j : ℕ} : measurable_set (antitoneseq f g ε i j) :=
measurable_set.Union (λ k, measurable_set.Union_Prop $ λ hk,
  measurable_set_lt measurable_const $ (hf k).dist hg)

private lemma antitoneseq_antitone {i : ℕ} :
  antitone (antitoneseq f g ε i) :=
λ j k hjk, bUnion_subset_bUnion (λ l hl, ⟨l, le_trans hjk hl, subset.refl _⟩)

theorem egorov {f : ℕ → α → β} {g : α → β} {s : set α} (hsm : measurable_set s) (hs : μ s < ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (ε : ℝ≥0∞) :
  ∃ t ⊆ s, μ t < ε ∧ tendsto_uniformly_on f g at_top t :=
begin
  sorry
end

end move

variables {α β ι : Type*} [normed_group β]

-- **Change doc-strings**

/-- A family `I` of (L₁-)functions is known as uniformly integrable if for all `ε > 0`, there
exists some `δ > 0` such that for all `f ∈ I` and measurable sets `s` with measure less than `δ`,
we have `∫ x in s, ∥f x∥ < ε`.

This is the measure theory verison of uniform integrability. -/
def unif_integrable {m : measurable_space α} (μ : measure α) (f : ι → α → β) : Prop :=
∀ ε : ℝ≥0∞, ∃ δ : ℝ≥0∞, ∀ i s, measurable_set s → μ s < δ →
snorm (set.indicator s (f i)) 1 μ < ε

/-- In probability theory, a family of functions is uniformly integrable if it is uniformly
integrable in the measure theory sense and is uniformly bounded. -/
def uniform_integrable {m : measurable_space α} [measurable_space β]
  (μ : measure α) (f : ι → α → β) : Prop :=
(∀ i, measurable (f i)) ∧ unif_integrable μ f ∧
  ∃ C : ℝ≥0, ∀ i, snorm (f i) 1 μ < C

variables {m : measurable_space α} {μ : measure α} [measurable_space β] {f : ι → α → β}

lemma uniform_integrable.mem_ℒp_one (hf : uniform_integrable μ f) (i : ι) :
  mem_ℒp (f i) 1 μ :=
⟨(hf.1 i).ae_measurable, let ⟨_, _, hC⟩ := hf.2 in lt_trans (hC i) ennreal.coe_lt_top⟩

end measure_theory
