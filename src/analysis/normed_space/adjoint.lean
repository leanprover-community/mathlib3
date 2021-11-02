/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Frédéric Dupuis
-/

import analysis.normed_space.dual

/-!
# Adjoint of operators on normed spaces

Given an operator `A : E →L[𝕜] F`, where `E` and `F` are normed spaces, its adjoint
`adjoint A : (dual 𝕜 F) →L[𝕜] (dual 𝕜 E)` is the operator that maps `ℓ : dual 𝕜 F` to
`ℓ.comp A`.

## Tags

adjoint
-/

open normed_space
noncomputable theory

variables {𝕜 E F : Type*} [is_R_or_C 𝕜]
variables [normed_group E] [normed_group F]
variables [normed_space 𝕜 E] [normed_space 𝕜 F]

/-- The adjoint of `A : E →L[𝕜] F` maps `ℓ : dual 𝕜 F` to `ℓ.comp A`.  -/
@[simps] def adjoint : (E →L[𝕜] F) →ₗᵢ[𝕜] ((dual 𝕜 F) →L[𝕜] (dual 𝕜 E)) :=
{ norm_map' := λ A, begin
    apply continuous_linear_map.op_norm_eq_of_bounds,
    { exact (norm_nonneg _) },
    { intros φ,
      rw mul_comm,
      exact continuous_linear_map.op_norm_comp_le φ A },
    { intros C hC h,
      apply continuous_linear_map.op_norm_le_bound _ hC,
      intros v,
      have : 0 ≤ C * ∥v∥ := mul_nonneg hC (norm_nonneg _),
      apply norm_le_dual_bound 𝕜 _ this,
      intros φ,
      calc _ ≤ C * ∥φ∥ * ∥v∥ : continuous_linear_map.le_of_op_norm_le _ (h φ) v
      ... = C * ∥v∥ * ∥φ∥ : by ring }
  end,
  .. (continuous_linear_map.compL 𝕜 E F 𝕜).flip }
