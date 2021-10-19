/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.function.conditional_expectation
import measure_theory.decomposition.radon_nikodym

/-! # Notations for probability theory

This file defines the following notations, for functions `X,Y`, measures `P, Q` defined on a
measurable space `m0`, and another measurable space structure `m` with `hm : m ≤ m0`,
- `P[X] = ∫ a, X a ∂P`
- `𝔼[X] = ∫ a, X a`
- `𝔼[X|hm]`: conditional expectation of `X` with respect to the measure `volume` and the
  measurable space `m`. The similar `P[X|hm]` for a measure `P` is defined in
  measure_theory.function.conditional_expectation.
- `X =ₐₛ Y`: `X =ᵐ[volume] Y`
- `X ≤ₐₛ Y`: `X ≤ᵐ[volume] Y`
- `∂P/∂Q = P.rn_deriv Q`

TODO: define the notation `ℙ s` for the probability of a set `s`, and decide whether it should be a
value in `ℝ`, `ℝ≥0` or `ℝ≥0∞`.
-/

open measure_theory

localized "notation `𝔼[` X `|` hm `]` := measure_theory.condexp hm volume X" in probability_theory

localized "notation P `[` X `]` := ∫ x, X x ∂P" in probability_theory

localized "notation `𝔼[` X `]` := ∫ a, X a" in probability_theory

localized "notation X `=ₐₛ`:50 Y:50 := X =ᵐ[volume] Y" in probability_theory

localized "notation X `≤ₐₛ`:50 Y:50 := X ≤ᵐ[volume] Y" in probability_theory

localized "notation `∂` P `/∂`:50 Q:50 := P.rn_deriv Q" in probability_theory
