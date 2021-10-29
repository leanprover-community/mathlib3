/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import analysis.inner_product_space.dual

/-!
# Adjoint of operators in inner product spaces

## Main results

## Notation

## Implementation notes

## Tags

## References

-/

noncomputable theory
open inner_product_space

variables {𝕜 E F : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]
variables [complete_space E] [complete_space F]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 F _ x y

def inner_right' (A : E →L[𝕜] F) (v : F) : E →L[𝕜] 𝕜 :=
linear_map.mk_continuous
  { to_fun := λ w, ⟪v, A w⟫,
    map_add' := λ x y, by { rw [continuous_linear_map.map_add], exact inner_add_right },
    map_smul' := λ c x, by
      simp only [inner_smul_right, algebra.id.smul_eq_mul, ring_hom.id_apply, continuous_linear_map.map_smul] }
  (∥A∥ * ∥v∥)
  begin
    intro x,
    have h₁ : ∥A x∥ ≤ ∥A∥ * ∥x∥ := continuous_linear_map.le_op_norm _ _,
    have h₂ := @norm_inner_le_norm 𝕜 F _ _ v (A x),
    have h₃ :=
      calc ∥⟪v, A x⟫∥ ≤ ∥v∥ * ∥A x∥       :  h₂
                  ... ≤ ∥v∥ * (∥A∥ * ∥x∥)  : by { mono, exact norm_nonneg _, exact norm_nonneg _ }
                   ... = ∥A∥ * ∥v∥ * ∥x∥    : by ring,
    simp only [h₃, linear_map.coe_mk],
  end

@[simp] lemma inner_right'_apply (A : E →L[𝕜] F) (v : F) (w : E) : inner_right' A v w = ⟪v, A w⟫ := rfl

example : E →L⋆[𝕜] E :=
linear_map.mk_continuous
{ to_fun := id,
  map_add' := sorry,
  map_smul' := begin
    sorry --can't figure out 𝕜 here
  end }
1
sorry


def inner_right_cl (A : E →L[𝕜] F) : F →L⋆[𝕜] E →L[𝕜] 𝕜 :=
linear_map.mk_continuous
{
  to_fun := λ v, inner_right' A v,
  map_add' := λ x y, by { ext w, simp only [inner_add_left, inner_right'_apply, continuous_linear_map.add_apply] },
  map_smul' := λ r x, begin

  end
}
1
begin
  sorry
end

--set_option trace.class_instances true
def adjoint' (A : E →L[𝕜] F) : F →L[𝕜] E :=
linear_map.mk_continuous
{ to_fun := λ v : F, (to_dual 𝕜 E).symm (inner_right' A v),
  map_add' := λ x y, begin
    simp [continuous_linear_map.map_add],
  end,
  map_smul' := sorry }
1
begin
  sorry
end


--def adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] E) :=
--{ to_fun := λ A, λ v, (to_dual 𝕜 E).symm (inner_right' v A),
--}
