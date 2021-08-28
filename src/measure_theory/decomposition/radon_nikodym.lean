/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.decomposition.lebesgue

/-!
# Radon-Nikodym theorem

This file proves the Radon-Nikodym theorem. The Radon-Nikodym theorem states that, given measures
`μ, ν`, if `have_lebesgue_decomposition μ ν`, then `μ` is absolutely continuous with respect to
`ν` if and only if there exists a measurable function `f : α → ℝ≥0∞` such that `μ = fν`.
In particular, we have `f = radon_nikodym_deriv μ ν`.

The Radon-Nikodym theorem will allow us to define many important concepts in probability theory,
most notably conditional expectations and probability cumulative functions.

## Main results

* `measure_theory.measure.absolutely_continuous_iff_with_density_radon_nikodym_deriv_eq` :
  the Radon-Nikodym theorem

## Tags

Radon-Nikodym theorem
-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α β : Type*} {m : measurable_space α}

namespace measure_theory

namespace measure

include m

lemma with_density_radon_nikodym_deriv_eq
  (μ ν : measure α) [have_lebesgue_decomposition μ ν] (h : μ ≪ ν) :
  ν.with_density (radon_nikodym_deriv μ ν) = μ :=
begin
  obtain ⟨hf₁, ⟨E, hE₁, hE₂, hE₃⟩, hadd⟩:= have_lebesgue_decomposition_spec μ ν,
  have : singular_part μ ν = 0,
  { refine le_antisymm (λ A hA, _) (measure.zero_le _),
    suffices : singular_part μ ν set.univ = 0,
    { rw [measure.coe_zero, pi.zero_apply, ← this],
      exact measure_mono (set.subset_univ _) },
    rw [← set.union_compl_self E, measure_union (@disjoint_compl_right _ E _) hE₁ hE₁.compl,
        hE₂, zero_add],
    have : (singular_part μ ν + ν.with_density (radon_nikodym_deriv μ ν)) Eᶜ = μ Eᶜ,
    { rw ← hadd },
    rw [measure.coe_add, pi.add_apply, h hE₃] at this,
    exact (add_eq_zero_iff.1 this).1 },
  rw [this, zero_add] at hadd,
  exact hadd.symm
end

/-- **The Radon-Nikodym theorem**: Given two measures `μ` and `ν`, if
`have_lebesgue_decomposition μ ν`, then `μ` is absolutely continuous to `ν` if and only if
`ν.with_density (radon_nikodym_deriv μ ν) = μ`. -/
theorem absolutely_continuous_iff_with_density_radon_nikodym_deriv_eq
  {μ ν : measure α} [have_lebesgue_decomposition μ ν] :
  μ ≪ ν ↔ ν.with_density (radon_nikodym_deriv μ ν) = μ :=
⟨with_density_radon_nikodym_deriv_eq μ ν, λ h, h ▸ with_density_absolutely_continuous _ _⟩

end measure

end measure_theory
