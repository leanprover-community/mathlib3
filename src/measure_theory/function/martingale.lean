/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.function.conditional_expectation

/-! # Filtrations and martingales

-/

open topological_space
open_locale nnreal ennreal measure_theory

namespace measure_theory

variables {α E ι : Type*} [measurable_space E]

def adapted (f : ι → α → E) (ℱ : ι → measurable_space α) : Prop := ∀ i, measurable[ℱ i] (f i)

def ae_adapted (f : ι → α → E) (ℱ : ι → measurable_space α) {m0 : measurable_space α}
  (μ : measure α) : Prop :=
∀ i, ae_measurable' (ℱ i) (f i) μ

def sigma_finite_filtration {ℱ_map : ι → measurable_space α} {m0 : measurable_space α}
  (ℱ : ∀ i, ℱ_map i ≤ m0) (μ : measure α) :
  Prop :=
∀ i, sigma_finite (μ.trim (ℱ i))

variables [preorder ι] [normed_group E] [normed_space ℝ E] [complete_space E] [borel_space E]
  [second_countable_topology E]

def martingale {ℱ_map : ι → measurable_space α} {m0 : measurable_space α} {μ : measure α}
  (f : ι → α → E) (ℱ : ∀ i, ℱ_map i ≤ m0) (h_sf : sigma_finite_filtration ℱ μ) : Prop :=
∀ i j, i ≤ j → by { haveI : sigma_finite (μ.trim (ℱ i)) := h_sf i, exact μ[f j | ℱ i] =ᵐ[μ] f i }

end measure_theory
