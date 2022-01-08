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

variables {α β : Type*} [normed_group β]

/-- A family `I` of (L₁-)functions is known as uniformly integrable if for all `ε > 0`, there
exists some `δ > 0` such that for all `f ∈ I` and measurable sets `s` with measure less than `δ`,
we have `∫ x in s, ∥f x∥ < ε`.

This is the measure theory verison of uniform integrability. -/
def unif_integrable {m : measurable_space α} (μ : measure α) (I : set (α → β)) : Prop :=
∀ ε : ℝ≥0∞, ∃ δ : ℝ≥0∞, ∀ (f ∈ I) (s : set α), measurable_set s → μ s < δ →
snorm (set.indicator s f) 1 μ < ε

/-- In probability theory, a family of functions is uniformly integrable if it is uniformly
integrable in the measure theory sense and is uniformly bounded. -/
def uniform_integrable {m : measurable_space α} (μ : measure α) (I : set (α → β)) : Prop :=
unif_integrable μ I ∧ ∃ C : ℝ≥0, ∀ f ∈ I, snorm f 1 μ < C

variables {m : measurable_space α} {μ : measure α} {I : set (α → β)}

lemma uniform_integrable.mem_ℒp_one [measurable_space β]
  (hI : uniform_integrable μ I) {f : α → β} (hf : f ∈ I) (hfm : ae_measurable f μ) :
  mem_ℒp f 1 μ :=
⟨hfm, let ⟨C, hC⟩ := hI.2 in lt_trans (hC f hf) ennreal.coe_lt_top⟩

end measure_theory
