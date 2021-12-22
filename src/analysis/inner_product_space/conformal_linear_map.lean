/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import analysis.normed_space.conformal_linear_map
import analysis.inner_product_space.basic

/-!
# Conformal maps between inner product spaces

In an inner product space, a map is conformal iff it preserves inner products up to a scalar factor.
-/

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F]

open linear_isometry continuous_linear_map
open_locale real_inner_product_space

lemma is_conformal_map_iff (f' : E →L[ℝ] F) :
  is_conformal_map f' ↔ ∃ (c : ℝ), 0 < c ∧
  ∀ (u v : E), ⟪f' u, f' v⟫ = (c : ℝ) * ⟪u, v⟫ :=
begin
  split,
  { rintros ⟨c₁, hc₁, li, h⟩,
    refine ⟨c₁ * c₁, mul_self_pos hc₁, λ u v, _⟩,
    simp only [h, pi.smul_apply, inner_map_map,
               real_inner_smul_left, real_inner_smul_right, mul_assoc], },
  { rintros ⟨c₁, hc₁, huv⟩,
    let c := real.sqrt c₁⁻¹,
    have hc : c ≠ 0 := λ w, by {simp only [c] at w;
      exact (real.sqrt_ne_zero'.mpr $ inv_pos.mpr hc₁) w},
    let f₁ := c • f',
    have minor : (f₁ : E → F) = c • f' := rfl,
    have minor' : (f' : E → F) = c⁻¹ • f₁ := by ext;
      simp_rw [minor, pi.smul_apply]; rw [smul_smul, inv_mul_cancel hc, one_smul],
    refine ⟨c⁻¹, inv_ne_zero hc, f₁.to_linear_map.isometry_of_inner (λ u v, _), minor'⟩,
    simp_rw [to_linear_map_eq_coe, continuous_linear_map.coe_coe, minor, pi.smul_apply],
    rw [real_inner_smul_left, real_inner_smul_right,
        huv u v, ← mul_assoc, ← mul_assoc,
        real.mul_self_sqrt $ le_of_lt $ inv_pos.mpr hc₁,
        inv_mul_cancel $ ne_of_gt hc₁, one_mul], },
end
