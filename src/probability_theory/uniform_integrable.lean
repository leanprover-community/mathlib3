/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/

import measure_theory.integral.set_integral

-- Probability should move to `measure_theory/integral`

noncomputable theory
open_locale classical measure_theory nnreal ennreal

namespace measure_theory

open set

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
