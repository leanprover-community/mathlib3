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

We then use this to put a C⋆-algebra structure on `E →L[𝕜] E` with the adjoint as the star
operation.

## Implementation notes

* The adjoint is defined as a conjugate-linear isometric equivalence between `E →L[𝕜] F` and
  `F →L[𝕜] E`. The continuous conjugate-linear version `adjoint_aux` is only an intermediate
  definition and is not meant to be used outside this file.

## Tags

adjoint

-/

noncomputable theory
open inner_product_space continuous_linear_map is_R_or_C
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

lemma apply_norm_sq_eq_inner_adjoint_left (A : E →L[𝕜] E) (x : E) : ∥A x∥^2 = re ⟪(A† * A) x, x⟫ :=
have h : ⟪(A† * A) x, x⟫ = ⟪A x, A x⟫ := by { rw [←adjoint_inner_left], refl },
by rw [h, ←inner_self_eq_norm_sq _]

lemma apply_norm_eq_sqrt_inner_adjoint_left (A : E →L[𝕜] E) (x : E) :
  ∥A x∥ = real.sqrt (re ⟪(A† * A) x, x⟫) :=
by rw [←apply_norm_sq_eq_inner_adjoint_left, real.sqrt_sq (norm_nonneg _)]

lemma apply_norm_sq_eq_inner_adjoint_right (A : E →L[𝕜] E) (x : E) : ∥A x∥^2 = re ⟪x, (A† * A) x⟫ :=
have h : ⟪x, (A† * A) x⟫ = ⟪A x, A x⟫ := by { rw [←adjoint_inner_right], refl },
by rw [h, ←inner_self_eq_norm_sq _]

lemma apply_norm_eq_sqrt_inner_adjoint_right (A : E →L[𝕜] E) (x : E) :
  ∥A x∥ = real.sqrt (re ⟪x, (A† * A) x⟫) :=
by rw [←apply_norm_sq_eq_inner_adjoint_right, real.sqrt_sq (norm_nonneg _)]

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all `x` and `y`. -/
lemma eq_adjoint_iff (A : E →L[𝕜] F) (B : F →L[𝕜] E) :
  A = B† ↔ (∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫) :=
begin
  refine ⟨λ h x y, by rw [h, adjoint_inner_left], λ h, _⟩,
  ext x,
  exact ext_inner_right 𝕜 (λ y, by simp only [adjoint_inner_left, h x y])
end

/-- `E →L[𝕜] E` is a star algebra with the adjoint as the star operation. -/
instance : has_star (E →L[𝕜] E) := ⟨adjoint⟩
instance : has_involutive_star (E →L[𝕜] E) := ⟨adjoint_adjoint⟩
instance : star_monoid (E →L[𝕜] E) := ⟨adjoint_comp⟩
instance : star_ring (E →L[𝕜] E) := ⟨linear_isometry_equiv.map_add adjoint⟩
instance : star_module 𝕜 (E →L[𝕜] E) := ⟨linear_isometry_equiv.map_smulₛₗ adjoint⟩

lemma star_eq_adjoint (A : E →L[𝕜] E) : star A = A† := rfl

instance : cstar_ring (E →L[𝕜] E) :=
⟨begin
  intros A,
  rw [star_eq_adjoint],
  refine le_antisymm _ _,
  { calc ∥A† * A∥ ≤ ∥A†∥ * ∥A∥      : op_norm_comp_le _ _
              ... = ∥A∥ * ∥A∥       : by rw [linear_isometry_equiv.norm_map] },
  { rw [←sq, ←real.sqrt_le_sqrt_iff (norm_nonneg _), real.sqrt_sq (norm_nonneg _)],
    refine op_norm_le_bound _ (real.sqrt_nonneg _) (λ x, _),
    have := calc
      re ⟪(A† * A) x, x⟫ ≤ ∥(A† * A) x∥ * ∥x∥     : re_inner_le_norm _ _
                    ...  ≤ ∥A† * A∥ * ∥x∥ * ∥x∥   : mul_le_mul_of_nonneg_right
                                                    (le_op_norm _ _) (norm_nonneg _),
    calc ∥A x∥ = real.sqrt (re ⟪(A† * A) x, x⟫)     : by rw [apply_norm_eq_sqrt_inner_adjoint_left]
          ...  ≤ real.sqrt (∥A† * A∥ * ∥x∥ * ∥x∥)   : real.sqrt_le_sqrt this
          ...  = real.sqrt (∥A† * A∥) * ∥x∥
            : by rw [mul_assoc, real.sqrt_mul (norm_nonneg _), real.sqrt_mul_self (norm_nonneg _)] }
end⟩

section real

variables {E' : Type*} {F' : Type*} [inner_product_space ℝ E'] [inner_product_space ℝ F']
variables [complete_space E'] [complete_space F']

lemma is_adjoint_pair (A : E' →L[ℝ] F') :
  bilin_form.is_adjoint_pair (bilin_form_of_real_inner : bilin_form ℝ E')
  (bilin_form_of_real_inner : bilin_form ℝ F') A (A†) :=
λ x y, by simp only [adjoint_inner_right, to_linear_map_eq_coe,
                     bilin_form_of_real_inner_apply, coe_coe]

end real

end continuous_linear_map
