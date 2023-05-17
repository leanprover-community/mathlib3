/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.complex.basic
import measure_theory.constructions.borel_space.basic

/-! # Equip `ℂ` with the Borel sigma-algebra -/

noncomputable theory

@[priority 900]
instance is_R_or_C.measurable_space {𝕜 : Type*} [is_R_or_C 𝕜] : measurable_space 𝕜 := borel 𝕜
@[priority 900]
instance is_R_or_C.borel_space {𝕜 : Type*} [is_R_or_C 𝕜] : borel_space 𝕜 := ⟨rfl⟩


instance complex.measurable_space : measurable_space ℂ := borel ℂ
instance complex.borel_space : borel_space ℂ := ⟨rfl⟩
