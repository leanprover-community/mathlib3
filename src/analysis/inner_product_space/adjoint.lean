/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth
-/

import analysis.inner_product_space.dual
import analysis.inner_product_space.pi_L2

/-!
# Adjoint of operators on Hilbert spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given an operator `A : E →L[𝕜] F`, where `E` and `F` are Hilbert spaces, its adjoint
`adjoint A : F →L[𝕜] E` is the unique operator such that `⟪x, A y⟫ = ⟪adjoint A x, y⟫` for all
`x` and `y`.

We then use this to put a C⋆-algebra structure on `E →L[𝕜] E` with the adjoint as the star
operation.

This construction is used to define an adjoint for linear maps (i.e. not continuous) between
finite dimensional spaces.

## Main definitions

* `continuous_linear_map.adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] E)`: the adjoint of a continuous
  linear map, bundled as a conjugate-linear isometric equivalence.
* `linear_map.adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] (F →ₗ[𝕜] E)`: the adjoint of a linear map between
  finite-dimensional spaces, this time only as a conjugate-linear equivalence, since there is no
  norm defined on these maps.

## Implementation notes

* The continuous conjugate-linear version `adjoint_aux` is only an intermediate
  definition and is not meant to be used outside this file.

## Tags

adjoint

-/

noncomputable theory
open is_R_or_C
open_locale complex_conjugate

variables {𝕜 E F G : Type*} [is_R_or_C 𝕜]
variables [normed_add_comm_group E] [normed_add_comm_group F] [normed_add_comm_group G]
variables [inner_product_space 𝕜 E] [inner_product_space 𝕜 F] [inner_product_space 𝕜 G]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

/-! ### Adjoint operator -/

open inner_product_space

namespace continuous_linear_map

variables [complete_space E] [complete_space G]

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
by rw [←inner_conj_symm, adjoint_aux_inner_left, inner_conj_symm]

variables [complete_space F]

lemma adjoint_aux_adjoint_aux (A : E →L[𝕜] F) : adjoint_aux (adjoint_aux A) = A :=
begin
  ext v,
  refine ext_inner_left 𝕜 (λ w, _),
  rw [adjoint_aux_inner_right, adjoint_aux_inner_left],
end

@[simp] lemma adjoint_aux_norm (A : E →L[𝕜] F) : ‖adjoint_aux A‖ = ‖A‖ :=
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

localized "postfix (name := adjoint) `†`:1000 := continuous_linear_map.adjoint" in inner_product

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

lemma apply_norm_sq_eq_inner_adjoint_left (A : E →L[𝕜] E) (x : E) : ‖A x‖^2 = re ⟪(A† * A) x, x⟫ :=
have h : ⟪(A† * A) x, x⟫ = ⟪A x, A x⟫ := by { rw [←adjoint_inner_left], refl },
by rw [h, ←inner_self_eq_norm_sq _]

lemma apply_norm_eq_sqrt_inner_adjoint_left (A : E →L[𝕜] E) (x : E) :
  ‖A x‖ = real.sqrt (re ⟪(A† * A) x, x⟫) :=
by rw [←apply_norm_sq_eq_inner_adjoint_left, real.sqrt_sq (norm_nonneg _)]

lemma apply_norm_sq_eq_inner_adjoint_right (A : E →L[𝕜] E) (x : E) : ‖A x‖^2 = re ⟪x, (A† * A) x⟫ :=
have h : ⟪x, (A† * A) x⟫ = ⟪A x, A x⟫ := by { rw [←adjoint_inner_right], refl },
by rw [h, ←inner_self_eq_norm_sq _]

lemma apply_norm_eq_sqrt_inner_adjoint_right (A : E →L[𝕜] E) (x : E) :
  ‖A x‖ = real.sqrt (re ⟪x, (A† * A) x⟫) :=
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

@[simp] lemma adjoint_id : (continuous_linear_map.id 𝕜 E).adjoint = continuous_linear_map.id 𝕜 E :=
begin
  refine eq.symm _,
  rw eq_adjoint_iff,
  simp,
end

lemma _root_.submodule.adjoint_subtypeL (U : submodule 𝕜 E)
  [complete_space U] :
  (U.subtypeL)† = orthogonal_projection U :=
begin
  symmetry,
  rw eq_adjoint_iff,
  intros x u,
  rw [U.coe_inner, inner_orthogonal_projection_left_eq_right,
      orthogonal_projection_mem_subspace_eq_self],
  refl
end

lemma _root_.submodule.adjoint_orthogonal_projection (U : submodule 𝕜 E)
  [complete_space U] :
  (orthogonal_projection U : E →L[𝕜] U)† = U.subtypeL :=
by rw [← U.adjoint_subtypeL, adjoint_adjoint]

/-- `E →L[𝕜] E` is a star algebra with the adjoint as the star operation. -/
instance : has_star (E →L[𝕜] E) := ⟨adjoint⟩
instance : has_involutive_star (E →L[𝕜] E) := ⟨adjoint_adjoint⟩
instance : star_semigroup (E →L[𝕜] E) := ⟨adjoint_comp⟩
instance : star_ring (E →L[𝕜] E) := ⟨linear_isometry_equiv.map_add adjoint⟩
instance : star_module 𝕜 (E →L[𝕜] E) := ⟨linear_isometry_equiv.map_smulₛₗ adjoint⟩

lemma star_eq_adjoint (A : E →L[𝕜] E) : star A = A† := rfl

/-- A continuous linear operator is self-adjoint iff it is equal to its adjoint. -/
lemma is_self_adjoint_iff' {A : E →L[𝕜] E} : is_self_adjoint A ↔ A.adjoint = A := iff.rfl

instance : cstar_ring (E →L[𝕜] E) :=
⟨begin
  intros A,
  rw [star_eq_adjoint],
  refine le_antisymm _ _,
  { calc ‖A† * A‖ ≤ ‖A†‖ * ‖A‖      : op_norm_comp_le _ _
              ... = ‖A‖ * ‖A‖       : by rw [linear_isometry_equiv.norm_map] },
  { rw [←sq, ←real.sqrt_le_sqrt_iff (norm_nonneg _), real.sqrt_sq (norm_nonneg _)],
    refine op_norm_le_bound _ (real.sqrt_nonneg _) (λ x, _),
    have := calc
      re ⟪(A† * A) x, x⟫ ≤ ‖(A† * A) x‖ * ‖x‖     : re_inner_le_norm _ _
                    ...  ≤ ‖A† * A‖ * ‖x‖ * ‖x‖   : mul_le_mul_of_nonneg_right
                                                    (le_op_norm _ _) (norm_nonneg _),
    calc ‖A x‖ = real.sqrt (re ⟪(A† * A) x, x⟫)     : by rw [apply_norm_eq_sqrt_inner_adjoint_left]
          ...  ≤ real.sqrt (‖A† * A‖ * ‖x‖ * ‖x‖)   : real.sqrt_le_sqrt this
          ...  = real.sqrt (‖A† * A‖) * ‖x‖
            : by rw [mul_assoc, real.sqrt_mul (norm_nonneg _), real.sqrt_mul_self (norm_nonneg _)] }
end⟩

section real

variables {E' : Type*} {F' : Type*}
variables [normed_add_comm_group E'] [normed_add_comm_group F']
variables [inner_product_space ℝ E'] [inner_product_space ℝ F']
variables [complete_space E'] [complete_space F']

-- Todo: Generalize this to `is_R_or_C`.
lemma is_adjoint_pair_inner (A : E' →L[ℝ] F') :
  linear_map.is_adjoint_pair (sesq_form_of_inner : E' →ₗ[ℝ] E' →ₗ[ℝ] ℝ)
  (sesq_form_of_inner : F' →ₗ[ℝ] F' →ₗ[ℝ] ℝ) A (A†) :=
λ x y, by simp only [sesq_form_of_inner_apply_apply, adjoint_inner_left, to_linear_map_eq_coe,
  coe_coe]

end real

end continuous_linear_map

/-! ### Self-adjoint operators -/

namespace is_self_adjoint

open continuous_linear_map

variables [complete_space E] [complete_space F]

lemma adjoint_eq {A : E →L[𝕜] E} (hA : is_self_adjoint A) : A.adjoint = A := hA

/-- Every self-adjoint operator on an inner product space is symmetric. -/
lemma is_symmetric {A : E →L[𝕜] E} (hA : is_self_adjoint A) :
  (A : E →ₗ[𝕜] E).is_symmetric :=
λ x y, by rw_mod_cast [←A.adjoint_inner_right, hA.adjoint_eq]

/-- Conjugating preserves self-adjointness -/
lemma conj_adjoint {T : E →L[𝕜] E} (hT : is_self_adjoint T) (S : E →L[𝕜] F) :
  is_self_adjoint (S ∘L T ∘L S.adjoint) :=
begin
  rw is_self_adjoint_iff' at ⊢ hT,
  simp only [hT, adjoint_comp, adjoint_adjoint],
  exact continuous_linear_map.comp_assoc _ _ _,
end

/-- Conjugating preserves self-adjointness -/
lemma adjoint_conj {T : E →L[𝕜] E} (hT : is_self_adjoint T) (S : F →L[𝕜] E) :
  is_self_adjoint (S.adjoint ∘L T ∘L S) :=
begin
  rw is_self_adjoint_iff' at ⊢ hT,
  simp only [hT, adjoint_comp, adjoint_adjoint],
  exact continuous_linear_map.comp_assoc _ _ _,
end

lemma _root_.continuous_linear_map.is_self_adjoint_iff_is_symmetric {A : E →L[𝕜] E} :
  is_self_adjoint A ↔ (A : E →ₗ[𝕜] E).is_symmetric :=
⟨λ hA, hA.is_symmetric, λ hA, ext $ λ x, ext_inner_right 𝕜 $
  λ y, (A.adjoint_inner_left y x).symm ▸ (hA x y).symm⟩

lemma _root_.linear_map.is_symmetric.is_self_adjoint {A : E →L[𝕜] E}
  (hA : (A : E →ₗ[𝕜] E).is_symmetric) : is_self_adjoint A :=
by rwa ←continuous_linear_map.is_self_adjoint_iff_is_symmetric at hA

/-- The orthogonal projection is self-adjoint. -/
lemma _root_.orthogonal_projection_is_self_adjoint (U : submodule 𝕜 E)
  [complete_space U] :
  is_self_adjoint (U.subtypeL ∘L orthogonal_projection U) :=
(orthogonal_projection_is_symmetric U).is_self_adjoint

lemma conj_orthogonal_projection {T : E →L[𝕜] E}
  (hT : is_self_adjoint T) (U : submodule 𝕜 E) [complete_space U] :
  is_self_adjoint (U.subtypeL ∘L orthogonal_projection U ∘L T ∘L U.subtypeL ∘L
    orthogonal_projection U) :=
begin
  rw ←continuous_linear_map.comp_assoc,
  nth_rewrite 0 ←(orthogonal_projection_is_self_adjoint U).adjoint_eq,
  refine hT.adjoint_conj _,
end

end is_self_adjoint

namespace linear_map

variables [complete_space E]
variables {T : E →ₗ[𝕜] E}

/-- The **Hellinger--Toeplitz theorem**: Construct a self-adjoint operator from an everywhere
  defined symmetric operator.-/
def is_symmetric.to_self_adjoint (hT : is_symmetric T) : self_adjoint (E →L[𝕜] E) :=
⟨⟨T, hT.continuous⟩, continuous_linear_map.is_self_adjoint_iff_is_symmetric.mpr hT⟩

lemma is_symmetric.coe_to_self_adjoint (hT : is_symmetric T) :
  (hT.to_self_adjoint : E →ₗ[𝕜] E) = T := rfl

lemma is_symmetric.to_self_adjoint_apply (hT : is_symmetric T) {x : E} :
  hT.to_self_adjoint x = T x := rfl

end linear_map

namespace linear_map

variables [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F] [finite_dimensional 𝕜 G]
local attribute [instance, priority 20] finite_dimensional.complete

/-- The adjoint of an operator from the finite-dimensional inner product space E to the finite-
dimensional inner product space F. -/
def adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] (F →ₗ[𝕜] E) :=
((linear_map.to_continuous_linear_map : (E →ₗ[𝕜] F) ≃ₗ[𝕜] (E →L[𝕜] F)).trans
  continuous_linear_map.adjoint.to_linear_equiv).trans
  linear_map.to_continuous_linear_map.symm

lemma adjoint_to_continuous_linear_map (A : E →ₗ[𝕜] F) :
  A.adjoint.to_continuous_linear_map = A.to_continuous_linear_map.adjoint := rfl

lemma adjoint_eq_to_clm_adjoint (A : E →ₗ[𝕜] F) :
  A.adjoint = A.to_continuous_linear_map.adjoint := rfl

/-- The fundamental property of the adjoint. -/
lemma adjoint_inner_left (A : E →ₗ[𝕜] F) (x : E) (y : F) : ⟪adjoint A y, x⟫ = ⟪y, A x⟫ :=
begin
  rw [←coe_to_continuous_linear_map A, adjoint_eq_to_clm_adjoint],
  exact continuous_linear_map.adjoint_inner_left _ x y,
end

/-- The fundamental property of the adjoint. -/
lemma adjoint_inner_right (A : E →ₗ[𝕜] F) (x : E) (y : F) : ⟪x, adjoint A y⟫ = ⟪A x, y⟫ :=
begin
  rw [←coe_to_continuous_linear_map A, adjoint_eq_to_clm_adjoint],
  exact continuous_linear_map.adjoint_inner_right _ x y,
end

/-- The adjoint is involutive -/
@[simp] lemma adjoint_adjoint (A : E →ₗ[𝕜] F) : A.adjoint.adjoint = A :=
begin
  ext v,
  refine ext_inner_left 𝕜 (λ w, _),
  rw [adjoint_inner_right, adjoint_inner_left],
end

/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
@[simp] lemma adjoint_comp (A : F →ₗ[𝕜] G) (B : E →ₗ[𝕜] F) :
  (A ∘ₗ B).adjoint = B.adjoint ∘ₗ A.adjoint :=
begin
  ext v,
  refine ext_inner_left 𝕜 (λ w, _),
  simp only [adjoint_inner_right, linear_map.coe_comp, function.comp_app],
end

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all `x` and `y`. -/
lemma eq_adjoint_iff (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
  A = B.adjoint ↔ (∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫) :=
begin
  refine ⟨λ h x y, by rw [h, adjoint_inner_left], λ h, _⟩,
  ext x,
  exact ext_inner_right 𝕜 (λ y, by simp only [adjoint_inner_left, h x y])
end

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all basis vectors `x` and `y`. -/
lemma eq_adjoint_iff_basis {ι₁ : Type*} {ι₂ : Type*} (b₁ : basis ι₁ 𝕜 E) (b₂ : basis ι₂ 𝕜 F)
  (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
  A = B.adjoint ↔ (∀ (i₁ : ι₁) (i₂ : ι₂), ⟪A (b₁ i₁), b₂ i₂⟫ = ⟪b₁ i₁, B (b₂ i₂)⟫) :=
begin
  refine ⟨λ h x y, by rw [h, adjoint_inner_left], λ h, _⟩,
  refine basis.ext b₁ (λ i₁, _),
  exact ext_inner_right_basis b₂ (λ i₂, by simp only [adjoint_inner_left, h i₁ i₂]),
end

lemma eq_adjoint_iff_basis_left {ι : Type*} (b : basis ι 𝕜 E) (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
  A = B.adjoint ↔ (∀ i y, ⟪A (b i), y⟫ = ⟪b i, B y⟫) :=
begin
  refine ⟨λ h x y, by rw [h, adjoint_inner_left], λ h, basis.ext b (λ i, _)⟩,
  exact ext_inner_right 𝕜 (λ y, by simp only [h i, adjoint_inner_left]),
end

lemma eq_adjoint_iff_basis_right {ι : Type*} (b : basis ι 𝕜 F) (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
  A = B.adjoint ↔ (∀ i x, ⟪A x, b i⟫ = ⟪x, B (b i)⟫) :=
begin
  refine ⟨λ h x y, by rw [h, adjoint_inner_left], λ h, _⟩,
  ext x,
  refine ext_inner_right_basis b (λ i, by simp only [h i, adjoint_inner_left]),
end

/-- `E →ₗ[𝕜] E` is a star algebra with the adjoint as the star operation. -/
instance : has_star (E →ₗ[𝕜] E) := ⟨adjoint⟩
instance : has_involutive_star (E →ₗ[𝕜] E) := ⟨adjoint_adjoint⟩
instance : star_semigroup (E →ₗ[𝕜] E) := ⟨adjoint_comp⟩
instance : star_ring (E →ₗ[𝕜] E) := ⟨linear_equiv.map_add adjoint⟩
instance : star_module 𝕜 (E →ₗ[𝕜] E) := ⟨linear_equiv.map_smulₛₗ adjoint⟩

lemma star_eq_adjoint (A : E →ₗ[𝕜] E) : star A = A.adjoint := rfl

/-- A continuous linear operator is self-adjoint iff it is equal to its adjoint. -/
lemma is_self_adjoint_iff' {A : E →ₗ[𝕜] E} : is_self_adjoint A ↔ A.adjoint = A := iff.rfl

lemma is_symmetric_iff_is_self_adjoint (A : E →ₗ[𝕜] E) :
  is_symmetric A ↔ is_self_adjoint A :=
by { rw [is_self_adjoint_iff', is_symmetric, ← linear_map.eq_adjoint_iff], exact eq_comm }

section real

variables {E' : Type*} {F' : Type*}
variables [normed_add_comm_group E'] [normed_add_comm_group F']
variables [inner_product_space ℝ E'] [inner_product_space ℝ F']
variables [finite_dimensional ℝ E'] [finite_dimensional ℝ F']

-- Todo: Generalize this to `is_R_or_C`.
lemma is_adjoint_pair_inner (A : E' →ₗ[ℝ] F') :
  is_adjoint_pair (sesq_form_of_inner : E' →ₗ[ℝ] E' →ₗ[ℝ] ℝ)
  (sesq_form_of_inner : F' →ₗ[ℝ] F' →ₗ[ℝ] ℝ) A A.adjoint :=
λ x y, by simp only [sesq_form_of_inner_apply_apply, adjoint_inner_left]

end real

/-- The Gram operator T†T is symmetric. -/
lemma is_symmetric_adjoint_mul_self (T : E →ₗ[𝕜] E) : is_symmetric (T.adjoint * T) :=
λ x y, by simp only [mul_apply, adjoint_inner_left, adjoint_inner_right]

/-- The Gram operator T†T is a positive operator. -/
lemma re_inner_adjoint_mul_self_nonneg (T : E →ₗ[𝕜] E) (x : E) :
  0 ≤ re ⟪ x, (T.adjoint * T) x ⟫ := by {simp only [mul_apply, adjoint_inner_right,
    inner_self_eq_norm_sq_to_K], norm_cast, exact sq_nonneg _}

@[simp] lemma im_inner_adjoint_mul_self_eq_zero (T : E →ₗ[𝕜] E) (x : E) :
  im ⟪ x, linear_map.adjoint T (T x) ⟫ = 0 := by {simp only [mul_apply,
    adjoint_inner_right, inner_self_eq_norm_sq_to_K], norm_cast}

end linear_map

namespace matrix
variables {m n : Type*} [fintype m] [decidable_eq m] [fintype n] [decidable_eq n]
open_locale complex_conjugate

/-- The adjoint of the linear map associated to a matrix is the linear map associated to the
conjugate transpose of that matrix. -/
lemma to_euclidean_lin_conj_transpose_eq_adjoint (A : matrix m n 𝕜) :
  A.conj_transpose.to_euclidean_lin = A.to_euclidean_lin.adjoint :=
begin
  rw linear_map.eq_adjoint_iff,
  intros x y,
  simp_rw [euclidean_space.inner_eq_star_dot_product, pi_Lp_equiv_to_euclidean_lin,
    to_lin'_apply, star_mul_vec, conj_transpose_conj_transpose, dot_product_mul_vec],
end

end matrix
