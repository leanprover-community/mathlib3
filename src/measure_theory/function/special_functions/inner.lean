/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import analysis.inner_product_space.basic
import measure_theory.constructions.borel_space

/-!
# Measurability of scalar products
-/

variables {α : Type*} {𝕜 : Type*} {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

@[measurability]
lemma measurable.inner {m : measurable_space α} [measurable_space E] [opens_measurable_space E]
  [topological_space.second_countable_topology E]
  {f g : α → E} (hf : measurable f) (hg : measurable g) :
  measurable (λ t, ⟪f t, g t⟫) :=
continuous.measurable2 continuous_inner hf hg

@[measurability]
lemma ae_measurable.inner {m : measurable_space α} [measurable_space E] [opens_measurable_space E]
  [topological_space.second_countable_topology E]
  {μ : measure_theory.measure α} {f g : α → E} (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ x, ⟪f x, g x⟫) μ :=
begin
  refine ⟨λ x, ⟪hf.mk f x, hg.mk g x⟫, hf.measurable_mk.inner hg.measurable_mk, _⟩,
  refine hf.ae_eq_mk.mp (hg.ae_eq_mk.mono (λ x hxg hxf, _)),
  dsimp only,
  congr,
  exacts [hxf, hxg],
end
