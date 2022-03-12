/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.function.conditional_expectation

/-! # Notations for probability theory

This file defines the following notations, for functions `X,Y`, measures `P, Q` defined on a
measurable space `m0`, and another measurable space structure `m` with `hm : m ≤ m0`,
- `P[X] = ∫ a, X a ∂P`
- `𝔼[X] = ∫ a, X a`
- `𝔼[X|m,hm]`: conditional expectation of `X` with respect to the measure `volume` and the
  measurable space `m`. The similar `P[X|m,hm]` for a measure `P` is defined in
  measure_theory.function.conditional_expectation.
- `X =ₐₛ Y`: `X =ᵐ[volume] Y`
- `X ≤ₐₛ Y`: `X ≤ᵐ[volume] Y`
- `∂P/∂Q = P.rn_deriv Q`
We note that the notation `∂P/∂Q` applies to three different cases, namely,
`measure_theory.measure.rn_deriv`, `measure_theory.signed_measure.rn_deriv` and
`measure_theory.complex_measure.rn_deriv`.

TODO: define the notation `ℙ s` for the probability of a set `s`, and decide whether it should be a
value in `ℝ`, `ℝ≥0` or `ℝ≥0∞`.
-/

open measure_theory

-- We define notations `𝔼[f|hm]` and `𝔼[f|m,hm]` for the conditional expectation of `f` with
-- respect to `m`. Both can be used in code but only the second one will be used by the goal view.
-- The first notation avoids the repetition of `m`, which is already present in `hm`. The second
-- one ensures that `m` stays visible in the goal view: when `hm` is complicated, it gets rendered
-- as `_` and the measurable space would not be visible in `𝔼[f|_]`, but is clear in `𝔼[f|m,_]`.
localized "notation `𝔼[` X `|` hm `]` :=
  measure_theory.condexp _ hm measure_theory.measure.volume X" in probability_theory
localized "notation `𝔼[` X `|` m `,` hm `]` :=
  measure_theory.condexp m hm measure_theory.measure.volume X" in probability_theory

localized "notation P `[` X `]` := ∫ x, X x ∂P" in probability_theory

localized "notation `𝔼[` X `]` := ∫ a, X a" in probability_theory

localized "notation X `=ₐₛ`:50 Y:50 := X =ᵐ[measure_theory.measure.volume] Y" in probability_theory

localized "notation X `≤ₐₛ`:50 Y:50 := X ≤ᵐ[measure_theory.measure.volume] Y" in probability_theory

localized "notation `∂` P `/∂`:50 Q:50 := P.rn_deriv Q" in probability_theory
