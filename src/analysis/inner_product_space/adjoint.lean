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

We then use this to put a star algebra structure on `E →L[𝕜] E` with the adjoint as the star
operation.

## Implementation notes

* The adjoint is defined as a conjugate-linear isometric equivalence between `E →L[𝕜] F` and
  `F →L[𝕜] E`. The continuous conjugate-linear version `adjoint_aux` is only an intermediate
  definition and is not meant to be used outside this file.

## TODO

* Prove the C⋆ property for `E →L[𝕜] E` to show that it is a C⋆-algebra.

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

/-- The adjoint, as a continuous conjugate-linear map.  This is only meant as an auxiliary
definition for the main definition `adjoint`, where this is bundled as a conjugate-linear isometric
equivalence. -/
def adjoint_aux : (E →L[𝕜] F) →L⋆[𝕜] (F →L[𝕜] E) :=
(continuous_linear_map.compSL _ _ _ _ _ ((to_dual 𝕜 E).symm : normed_space.dual 𝕜 E →L⋆[𝕜] E)).comp
  (to_sesq_form : (E →L[𝕜] F) →L[𝕜] F →L⋆[𝕜] normed_space.dual 𝕜 E)

@[simp] lemma adjoint_aux_apply (A : E →L[𝕜] F) (x : F) :
  adjoint_aux A x = ((to_dual 𝕜 E).symm : (normed_space.dual 𝕜 E) → E) ((to_sesq_form A) x) := rfl

lemma adjoint_aux_inner_left (A : E →L[𝕜] F) (x : E) (y : F) : ⟪adjoint_aux A y, x⟫ = ⟪y, A x⟫ :=
by { simp only [adjoint_aux_apply, to_dual_symm_apply, to_sesq_form_apply_coe, coe_comp',
                innerSL_apply_coe]}

lemma adjoint_aux_inner_right (A : E →L[𝕜] F) (x : E) (y : F) : ⟪x, adjoint_aux A y⟫ = ⟪A x, y⟫ :=
by rw [←inner_conj_sym, adjoint_aux_inner_left, inner_conj_sym]

variables [complete_space F]

lemma adjoint_aux_adjoint_aux (A : E →L[𝕜] F) : adjoint_aux (adjoint_aux A) = A :=
begin
  ext v,
  refine ext_inner_left 𝕜 (λ w, _),
  rw [adjoint_aux_inner_right, adjoint_aux_inner_left],
end

@[simp] lemma adjoint_aux_norm (A : E →L[𝕜] F) : ∥adjoint_aux A∥ = ∥A∥ :=
begin
  refine le_antisymm _ _,
  { refine continuous_linear_map.op_norm_le_bound _ (norm_nonneg _) (λ x, _),
    rw [adjoint_aux_apply, linear_isometry_equiv.norm_map],
    exact to_sesq_form_apply_norm_le },
  { nth_rewrite_lhs 0 [←adjoint_aux_adjoint_aux A],
    refine continuous_linear_map.op_norm_le_bound _ (norm_nonneg _) (λ x, _),
    rw [adjoint_aux_apply, linear_isometry_equiv.norm_map],
    exact to_sesq_form_apply_norm_le }
end

/-- The adjoint of a bounded operator from Hilbert space E to Hilbert space F. -/
def adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] E) :=
linear_isometry_equiv.of_surjective
{ norm_map' := adjoint_aux_norm,
  ..adjoint_aux }
(λ A, ⟨adjoint_aux A, adjoint_aux_adjoint_aux A⟩)

localized "postfix `†`:1000 := adjoint" in inner_product

/-- The fundamental property of the adjoint. -/
lemma adjoint_inner_left (A : E →L[𝕜] F) (x : E) (y : F) : ⟪A† y, x⟫ = ⟪y, A x⟫ :=
adjoint_aux_inner_left A x y

/-- The fundamental property of the adjoint. -/
lemma adjoint_inner_right (A : E →L[𝕜] F) (x : E) (y : F) : ⟪x, A† y⟫ = ⟪A x, y⟫ :=
adjoint_aux_inner_right A x y

/-- The adjoint is involutive -/
@[simp] lemma adjoint_adjoint (A : E →L[𝕜] F) : A†† = A :=
adjoint_aux_adjoint_aux A

/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
@[simp] lemma adjoint_comp (A : F →L[𝕜] G) (B : E →L[𝕜] F) : (A ∘L B)† = B† ∘L A† :=
begin
  ext v,
  refine ext_inner_left 𝕜 (λ w, _),
  simp only [adjoint_inner_right, continuous_linear_map.coe_comp', function.comp_app],
end

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all `x` and `y`. -/
lemma eq_adjoint_iff (A : E →L[𝕜] F) (B : F →L[𝕜] E) :
  (∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫) ↔ A = B† :=
begin
  refine ⟨λ h, _, λ h x y, by rw [h, adjoint_inner_left]⟩,
  ext x,
  exact ext_inner_right 𝕜 (λ y, by simp only [adjoint_inner_left, h x y])
end

/-- `E →L[𝕜] E` is a star algebra with the adjoint as the star operation. -/
instance : has_star (E →L[𝕜] E) := ⟨adjoint⟩
instance : has_involutive_star (E →L[𝕜] E) := ⟨adjoint_adjoint⟩
instance : star_monoid (E →L[𝕜] E) := ⟨adjoint_comp⟩
instance : star_ring (E →L[𝕜] E) := ⟨linear_isometry_equiv.map_add adjoint⟩
instance : star_module 𝕜 (E →L[𝕜] E) := ⟨linear_isometry_equiv.map_smulₛₗ adjoint⟩

section real

variables {E' : Type*} {F' : Type*} [inner_product_space ℝ E'] [inner_product_space ℝ F']
variables [complete_space E'] [complete_space F']

lemma is_adjoint_pair (A : E' →L[ℝ] F') :
  bilin_form.is_adjoint_pair (bilin_form_of_real_inner : bilin_form ℝ E')
  (bilin_form_of_real_inner : bilin_form ℝ F') A.to_linear_map (A†).to_linear_map :=
λ x y, by simp only [adjoint_inner_right, to_linear_map_eq_coe,
                     bilin_form_of_real_inner_apply, coe_coe]

end real

end continuous_linear_map
