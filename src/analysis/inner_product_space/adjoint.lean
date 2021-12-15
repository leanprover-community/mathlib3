/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth
-/

import analysis.inner_product_space.dual

/-!
# Adjoint of operators on Hilbert spaces

Given an operator `A : E →L[𝕜] F`, where `E` and `F` are Hilbert spaces, its adjoint
`adjoint A : F →L[𝕜] E` is the unique operator such that `⟪x, A y⟫ = ⟪adjoint A x, y⟫` for all
`x` and `y`.

## Implementation notes

* The adjoint is defined as a conjugate-linear isometric equivalence between `E →L[𝕜] F` and
  `F →L[𝕜] E`. The bare function `adjoint'` is only an intermediate definition and is not meant
  to be used outside this file.

## Tags

adjoint

-/

noncomputable theory
open inner_product_space continuous_linear_map
open_locale complex_conjugate

variables {𝕜 E F G : Type*} [is_R_or_C 𝕜]
variables [inner_product_space 𝕜 E] [inner_product_space 𝕜 F] [inner_product_space 𝕜 G]
variables [complete_space E] [complete_space G]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

namespace continuous_linear_map

/-- The adjoint, as a bare function. This is only meant as an auxiliary definition for
the main definition `adjoint`, where this is bundled as a conjugate-linear isometric
equivalence. -/
@[simps] def adjoint' (A : E →L[𝕜] F) : F →L[𝕜] E :=
((to_dual 𝕜 E).symm : (normed_space.dual 𝕜 E) →L⋆[𝕜] E).comp (to_sesq_formₗ A)

lemma adjoint'_inner_left {A : E →L[𝕜] F} {x : E} {y : F} : ⟪adjoint' A y, x⟫ = ⟪y, A x⟫ :=
by { simp only [adjoint'_apply, to_dual_symm_apply], refl }

lemma adjoint'_inner_right {A : E →L[𝕜] F} {x : E} {y : F} : ⟪x, adjoint' A y⟫ = ⟪A x, y⟫ :=
by rw [←inner_conj_sym, adjoint'_inner_left, inner_conj_sym]

variables [complete_space F]

lemma adjoint'_adjoint'_apply (A : E →L[𝕜] F) : adjoint' (adjoint' A) = A :=
begin
  ext v,
  refine ext_inner_left 𝕜 (λ w, _),
  rw [adjoint'_inner_right, adjoint'_inner_left],
end

lemma adjoint'_norm {A : E →L[𝕜] F} : ∥adjoint' A∥ = ∥A∥ :=
begin
  refine le_antisymm _ _,
  { refine continuous_linear_map.op_norm_le_bound _ (norm_nonneg _) (λ x, _),
    rw [adjoint'_apply, linear_isometry_equiv.norm_map],
    exact to_sesq_form_apply_norm_le },
  { nth_rewrite_lhs 0 [←adjoint'_adjoint'_apply A],
    refine continuous_linear_map.op_norm_le_bound _ (norm_nonneg _) (λ x, _),
    rw [adjoint'_apply, linear_isometry_equiv.norm_map],
    exact to_sesq_form_apply_norm_le }
end

/-- The adjoint of a bounded operator from Hilbert space E to Hilbert space F. -/
def adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] E) :=
linear_isometry_equiv.of_surjective
{ to_fun := adjoint',
  map_add' := λ A B, by simp only [adjoint', linear_map.map_add, comp_add],
  map_smul' := λ r A, by simp only [adjoint', linear_map.map_smulₛₗ, ring_hom.id_apply,
                                    comp_smulₛₗ],
  norm_map' := λ A, adjoint'_norm }
(λ A, ⟨adjoint' A, adjoint'_adjoint'_apply A⟩)

/-- The fundamental property of the adjoint. -/
lemma adjoint_inner_left {A : E →L[𝕜] F} {x : E} {y : F} : ⟪adjoint A y, x⟫ = ⟪y, A x⟫ :=
adjoint'_inner_left

/-- The fundamental property of the adjoint. -/
lemma adjoint_inner_right {A : E →L[𝕜] F} {x : E} {y : F} : ⟪x, adjoint A y⟫ = ⟪A x, y⟫ :=
adjoint'_inner_right

/-- The adjoint is involutive -/
@[simp] lemma adjoint_adjoint_apply {A : E →L[𝕜] F} : adjoint (adjoint A) = A :=
adjoint'_adjoint'_apply A

/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
@[simp] lemma adjoint_comp {A : F →L[𝕜] G} {B : E →L[𝕜] F} :
  adjoint (A ∘L B) = (adjoint B) ∘L (adjoint A) :=
begin
  ext v,
  refine ext_inner_left 𝕜 (λ w, _),
  simp only [adjoint_inner_right, continuous_linear_map.coe_comp', function.comp_app],
end

/-- `E →L[𝕜] E` is a star algebra with the adjoint as the star operation. -/
instance : has_star (E →L[𝕜] E) := ⟨adjoint⟩
instance : has_involutive_star (E →L[𝕜] E) := ⟨λ _, adjoint_adjoint_apply⟩
instance : star_monoid (E →L[𝕜] E) := ⟨λ _ _, adjoint_comp⟩
instance : star_ring (E →L[𝕜] E) := ⟨linear_isometry_equiv.map_add adjoint⟩
instance : star_module 𝕜 (E →L[𝕜] E) := ⟨linear_isometry_equiv.map_smulₛₗ adjoint⟩

end continuous_linear_map
