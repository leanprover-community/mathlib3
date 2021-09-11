/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.function.conditional_expectation

/-! # Filtrations and martingales

-/

open_locale nnreal ennreal measure_theory

namespace measure_theory

variables {α E ι : Type*} [measurable_space E]

def adapted (f : ι → α → E) (ℱ : ι → measurable_space α) : Prop := ∀ i, measurable[ℱ i] (f i)

def ae_adapted (f : ι → α → E) (ℱ : ι → measurable_space α) {m0 : measurable_space α}
  (μ : measure α) : Prop :=
∀ i, ae_measurable' (ℱ i) (f i) μ

def sigma_finite_filtration (ℱ : ι → measurable_space α) {m0 : measurable_space α}
  (h_le : ∀ i, ℱ i ≤ m0) (μ : measure α) :
  Prop :=
∀ i, sigma_finite (μ.trim (h_le i))

end measure_theory
