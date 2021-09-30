/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.function.conditional_expectation
import measure_theory.decomposition.radon_nikodym

/-! # Notations for probability theory -/

open measure_theory measure_theory.measure topological_space

-- The related notation `P[ X | hm] := measure_theory.condexp hm P X` is defined in
-- measure_theory.function.conditional_expectation.
localized "notation `𝔼[` X `|` hm `]` := measure_theory.condexp hm volume X" in probability_theory

-- The usual expectation notation `𝔼[X]` does not carry information about the measure used, hence
-- we reserve it for the `volume` measure, and use the similar `P[X]` for the expectation under `P`.
localized "notation P `[` X `]` := ∫ x, X x ∂P" in probability_theory

localized "notation `𝔼[` X `]` := ∫ a, X a" in probability_theory

localized "notation X `=ₐₛ`:50 Y:50 := X =ᵐ[volume] Y" in probability_theory

localized "notation X `≤ₐₛ`:50 Y:50 := X ≤ᵐ[volume] Y" in probability_theory

localized "notation `∂` P `/∂`:50 P':50 := P.rn_deriv P'" in probability_theory

section examples

open_locale probability_theory

variables {α E : Type*} [measure_space α] {P P' : measure α} [measurable_space E] [normed_group E]
  [normed_space ℝ E] [borel_space E] [second_countable_topology E] [complete_space E] {X Y : α → E}

example : P[X] = ∫ a, X a ∂P := rfl

example : 𝔼[X] = volume[X] := rfl

example : X =ₐₛ Y ↔ X =ᵐ[volume] Y := iff.rfl

example : ∂P/∂P' = P.rn_deriv P' := rfl

/-- TODO: how may I remove the parentheses? Also: is this an existing lemma? -/
example [have_lebesgue_decomposition P P'] (h : P ≪ P') : ∫⁻ a, (∂P/∂P') a ∂P' = P set.univ :=
by rw [← set_lintegral_univ, ← with_density_apply _ measurable_set.univ,
  with_density_rn_deriv_eq _ _ h]

end examples
