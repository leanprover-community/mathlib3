/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import analysis.normed_space.conformal_linear_map
import analysis.inner_product_space.basic

/-!
# Conformal maps between inner product spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In an inner product space, a map is conformal iff it preserves inner products up to a scalar factor.
-/

variables {E F : Type*}
variables [normed_add_comm_group E] [normed_add_comm_group F]
variables [inner_product_space ℝ E] [inner_product_space ℝ F]

open linear_isometry continuous_linear_map
open_locale real_inner_product_space

/-- A map between two inner product spaces is a conformal map if and only if it preserves inner
products up to a scalar factor, i.e., there exists a positive `c : ℝ` such that `⟪f u, f v⟫ = c *
⟪u, v⟫` for all `u`, `v`. -/
lemma is_conformal_map_iff (f : E →L[ℝ] F) :
  is_conformal_map f ↔ ∃ (c : ℝ), 0 < c ∧ ∀ (u v : E), ⟪f u, f v⟫ = c * ⟪u, v⟫ :=
begin
  split,
  { rintros ⟨c₁, hc₁, li, rfl⟩,
    refine ⟨c₁ * c₁, mul_self_pos.2 hc₁, λ u v, _⟩,
    simp only [real_inner_smul_left, real_inner_smul_right, mul_assoc, coe_smul',
      coe_to_continuous_linear_map, pi.smul_apply, inner_map_map] },
  { rintros ⟨c₁, hc₁, huv⟩,
    obtain ⟨c, hc, rfl⟩ : ∃ c : ℝ, 0 < c ∧ c₁ = c * c,
      from ⟨real.sqrt c₁, real.sqrt_pos.2 hc₁, (real.mul_self_sqrt hc₁.le).symm⟩,
    refine ⟨c, hc.ne', (c⁻¹ • f : E →ₗ[ℝ] F).isometry_of_inner (λ u v, _), _⟩,
    { simp only [real_inner_smul_left, real_inner_smul_right, huv, mul_assoc, coe_smul,
        inv_mul_cancel_left₀ hc.ne', linear_map.smul_apply, continuous_linear_map.coe_coe] },
    { ext1 x,
      exact (smul_inv_smul₀ hc.ne' (f x)).symm } }
end
