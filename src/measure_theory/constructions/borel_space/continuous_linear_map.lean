/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import analysis.normed_space.finite_dimension
import measure_theory.constructions.borel_space.basic

/-!
# Measurable functions in normed spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

open measure_theory

variables {α : Type*} [measurable_space α]

namespace continuous_linear_map

variables {𝕜 : Type*} [normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] [measurable_space E]
  [opens_measurable_space E] {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  [measurable_space F] [borel_space F]

@[measurability]
protected lemma measurable (L : E →L[𝕜] F) : measurable L :=
L.continuous.measurable

lemma measurable_comp (L : E →L[𝕜] F) {φ : α → E} (φ_meas : measurable φ) :
  measurable (λ (a : α), L (φ a)) :=
L.measurable.comp φ_meas

end continuous_linear_map

namespace continuous_linear_map

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
          {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]

instance : measurable_space (E →L[𝕜] F) := borel _

instance : borel_space (E →L[𝕜] F) := ⟨rfl⟩

@[measurability]
lemma measurable_apply [measurable_space F] [borel_space F] (x : E) :
  measurable (λ f : E →L[𝕜] F, f x) :=
(apply 𝕜 F x).continuous.measurable

@[measurability]
lemma measurable_apply' [measurable_space E] [opens_measurable_space E]
  [measurable_space F] [borel_space F] :
  measurable (λ (x : E) (f : E →L[𝕜] F), f x) :=
measurable_pi_lambda _ $ λ f, f.measurable

@[measurability]
lemma measurable_coe [measurable_space F] [borel_space F] :
  measurable (λ (f : E →L[𝕜] F) (x : E), f x) :=
measurable_pi_lambda _ measurable_apply

end continuous_linear_map

section continuous_linear_map_nontrivially_normed_field

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] [measurable_space E]
  [borel_space E] {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]

@[measurability]
lemma measurable.apply_continuous_linear_map  {φ : α → F →L[𝕜] E} (hφ : measurable φ) (v : F) :
  measurable (λ a, φ a v) :=
(continuous_linear_map.apply 𝕜 E v).measurable.comp hφ

@[measurability]
lemma ae_measurable.apply_continuous_linear_map {φ : α → F →L[𝕜] E} {μ : measure α}
  (hφ : ae_measurable φ μ) (v : F) : ae_measurable (λ a, φ a v) μ :=
(continuous_linear_map.apply 𝕜 E v).measurable.comp_ae_measurable hφ

end continuous_linear_map_nontrivially_normed_field

section normed_space
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜] [complete_space 𝕜] [measurable_space 𝕜]
variables [borel_space 𝕜] {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  [measurable_space E] [borel_space E]

lemma measurable_smul_const {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
  measurable (λ x, f x • c) ↔ measurable f :=
(closed_embedding_smul_left hc).measurable_embedding.measurable_comp_iff

lemma ae_measurable_smul_const {f : α → 𝕜} {μ : measure α} {c : E} (hc : c ≠ 0) :
  ae_measurable (λ x, f x • c) μ ↔ ae_measurable f μ :=
(closed_embedding_smul_left hc).measurable_embedding.ae_measurable_comp_iff

end normed_space
