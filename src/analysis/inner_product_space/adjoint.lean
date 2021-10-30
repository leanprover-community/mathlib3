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
open_locale complex_conjugate

variables {𝕜 E F : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]
variables [complete_space E] [complete_space F]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 F _ x y

/-- Find a better name -/
def inner_right' (A : E →L[𝕜] F) (v : F) : E →L[𝕜] 𝕜 :=
linear_map.mk_continuous
  { to_fun := λ w, ⟪v, A w⟫,
    map_add' := λ x y, by { rw [continuous_linear_map.map_add], exact inner_add_right },
    map_smul' := λ c x, by
      simp only [inner_smul_right, algebra.id.smul_eq_mul, ring_hom.id_apply,
                 continuous_linear_map.map_smul] }
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

@[simp] lemma inner_right'_apply (A : E →L[𝕜] F) (v : F) (w : E) :
  inner_right' A v w = ⟪v, A w⟫ := rfl

lemma inner_right'_norm (A : E →L[𝕜] F) (v : F) : ∥inner_right' A v∥ ≤ ∥A∥ * ∥v∥ :=
begin
  refine continuous_linear_map.op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _,
  simp only [inner_right'_apply],
  intro x,
  have h₁ : ∥A x∥ ≤ ∥A∥ * ∥x∥ := continuous_linear_map.le_op_norm _ _,
  have h₂ := @norm_inner_le_norm 𝕜 F _ _ v (A x),
  calc ∥⟪v, A x⟫∥ ≤ ∥v∥ * ∥A x∥       :  h₂
              ... ≤ ∥v∥ * (∥A∥ * ∥x∥)  : by { mono, exact norm_nonneg _, exact norm_nonneg _ }
              ... = ∥A∥ * ∥v∥ * ∥x∥    : by ring,
end

/-- Find a better name -/
@[simps] def inner_right'ₛₗ (A : E →L[𝕜] F) : F →ₗ⋆[𝕜] E →L[𝕜] 𝕜 :=
{ to_fun := λ v, inner_right' A v,
  map_add' := λ x y, by { ext w, simp only [inner_add_left, inner_right'_apply,
                                            continuous_linear_map.add_apply] },
  map_smul' := λ r x, by { ext z, simp only [inner_smul_left, algebra.id.smul_eq_mul,
                                    inner_right'_apply, pi.smul_apply, ring_equiv.coe_to_ring_hom,
                                    continuous_linear_map.coe_smul'] } }

lemma inner_right'ₛₗ_map_smul {r : 𝕜} {A : E →L[𝕜] F} {v : F} :
  inner_right'ₛₗ (r • A) v = r • inner_right'ₛₗ A v :=
begin
  ext w,
  simp only [inner_smul_right, inner_right'ₛₗ_apply, algebra.id.smul_eq_mul,
    inner_right'_apply, pi.smul_apply, continuous_linear_map.coe_smul'],
end

/-- The adjoint, as a bare function -/
@[simps] def adjoint' (A : E →L[𝕜] F) : F →L[𝕜] E :=
linear_map.mk_continuous
{ to_fun := λ v : F, (to_dual 𝕜 E).symm (inner_right'ₛₗ A v),
  map_add' := λ x y, by simp only [linear_isometry_equiv.map_add, linear_map.map_add],
  map_smul' := λ r x, by simp only [linear_map.map_smulₛₗ, linear_isometry_equiv.map_smulₛₗ,
                                    star_ring_aut_self_apply r, ring_hom.id_apply,
                                    ring_equiv.coe_to_ring_hom] }
∥A∥
(λ x, by simp only [linear_isometry_equiv.norm_map, inner_right'_norm,
                    inner_right'ₛₗ_apply, linear_map.coe_mk])

@[simp] lemma adjoint'_apply {A : E →L[𝕜] F} {v : F} :
  adjoint' A v = (to_dual 𝕜 E).symm (inner_right'ₛₗ A v) := rfl

lemma adjoint'_adjoint' (A : E →L[𝕜] F) : adjoint' (adjoint' A) = A :=
begin
  sorry
end

--set_option trace.simplify.rewrite true

/-- The adjoint -/
def adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] E) :=
linear_isometry_equiv.of_surjective
{ to_fun := adjoint',
  map_add' := λ A B,
  begin
    ext v,
    simp only [adjoint'_apply, inner_right'ₛₗ_apply, continuous_linear_map.add_apply,
              ←linear_isometry_equiv.map_add, linear_isometry_equiv.map_eq_iff],
    ext w,
    simp only [inner_add_right, inner_right'_apply, continuous_linear_map.add_apply],
  end,
  map_smul' := λ r A,
  begin
    ext v,
    simp only [adjoint'_apply, inner_right'ₛₗ_map_smul, linear_isometry_equiv.map_smulₛₗ,
               ring_equiv.coe_to_ring_hom, continuous_linear_map.coe_smul', pi.smul_apply],
  end,
  norm_map' := λ A, begin
    sorry
  end }
begin  -- prove surjectivity
  intro A,
  refine ⟨adjoint' A, _⟩,
  sorry,
end
