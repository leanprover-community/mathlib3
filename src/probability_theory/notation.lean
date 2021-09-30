/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.function.conditional_expectation
import measure_theory.decomposition.radon_nikodym

/-! # Notations for probability theory -/

open measure_theory topological_space

-- The related notation `ℙ[ X | hm] := measure_theory.condexp hm ℙ X` is defined in
-- measure_theory.function.conditional_expectation.
localized "notation `𝔼[` X `|` hm `]` := measure_theory.condexp hm volume X" in probability_theory

-- The usual expectation notation `𝔼[X]` does not carry information about the measure used, hence
-- we reserve it for the `volume` measure, and use the similar `ℙ[X]` for the expectation under `ℙ`.
localized "notation ℙ `[` X `]` := ∫ x, X x ∂ℙ" in probability_theory

localized "notation `𝔼[` X `]` := ∫ a, X a" in probability_theory

localized "notation X `=ₐₛ`:50 Y:50 := X =ᵐ[volume] Y" in probability_theory

localized "notation X `≤ₐₛ`:50 Y:50 := X ≤ᵐ[volume] Y" in probability_theory

localized "notation `∂` ℙ `/∂`:50 ℙ':50 := ℙ.rn_deriv ℙ'" in probability_theory

section examples

open_locale probability_theory

variables {α E : Type*} [measure_space α] {ℙ ℙ' : measure α} [measurable_space E] [normed_group E]
  [normed_space ℝ E] [borel_space E] [second_countable_topology E] [complete_space E] {X Y : α → E}

example : ℙ[X] = ∫ a, X a ∂ℙ := rfl

example : 𝔼[X] = volume[X] := rfl

example : X =ₐₛ Y ↔ X =ᵐ[volume] Y := iff.rfl

example : ∂ℙ/∂ℙ' = ℙ.rn_deriv ℙ' := rfl

end examples
