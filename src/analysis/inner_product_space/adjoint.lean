/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth
-/

import analysis.normed_space.adjoint
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
open inner_product_space
open_locale complex_conjugate

variables {𝕜 E F G : Type*} [is_R_or_C 𝕜]
variables [inner_product_space 𝕜 E] [inner_product_space 𝕜 F] [inner_product_space 𝕜 G]
variables [complete_space E] [complete_space F] [complete_space G]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

namespace inner_product_space

def innerₛₗ : E →L⋆[𝕜] E →L[𝕜] 𝕜 :=
linear_map.mk_continuous
{ to_fun := λ v, inner_right v,
  map_add' := λ v w, by { ext z, simp only [inner_add_left, inner_right_apply,
                                            continuous_linear_map.add_apply] },
  map_smul' := λ r v, by { ext z, exact inner_smul_left } }
1
begin
  intros v,
  refine continuous_linear_map.op_norm_le_bound _ (mul_nonneg zero_le_one (norm_nonneg _)) (λ w, _),
  simp only [norm_inner_le_norm, inner_right_apply, one_mul, linear_map.coe_mk],
end

lemma to_dual_comp_norm (A : E →L[𝕜] F) (v : F) : ∥(to_dual 𝕜 F v).comp A∥ ≤ ∥A∥ * ∥v∥ :=
begin
  refine continuous_linear_map.op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _,
  intro x,
  have h₁ : ∥A x∥ ≤ ∥A∥ * ∥x∥ := continuous_linear_map.le_op_norm _ _,
  have h₂ := @norm_inner_le_norm 𝕜 F _ _ v (A x),
  calc ∥⟪v, A x⟫∥ ≤ ∥v∥ * ∥A x∥       :  h₂
              ... ≤ ∥v∥ * (∥A∥ * ∥x∥)  : by { mono, exact norm_nonneg _, exact norm_nonneg _ }
              ... = ∥A∥ * ∥v∥ * ∥x∥    : by ring,
end

--set_option trace.simplify.rewrite true
/-- The function `λ v w, ⟪v, A w⟫` for a given operator `A` -/
def inner_left_right : (E →L[𝕜] F) →+ F →L⋆[𝕜] E →L[𝕜] 𝕜 :=
{ to_fun := λ A,
  (linear_map.mk_continuous
  { to_fun := λ v, (to_dual 𝕜 F v).comp A,
    map_add' := λ x y, by { ext w, simp only [continuous_linear_map.add_apply,
            continuous_linear_map.coe_comp', function.comp_app, linear_isometry_equiv.map_add]},
    map_smul' := λ r x, by { ext z, simp [inner_smul_left] } }
  ∥A∥
  (λ x, to_dual_comp_norm A x)),
  map_zero' := by { simp only [continuous_linear_map.comp_zero], refl },
  map_add' := λ A B, begin
    simp only [continuous_linear_map.comp_add],
    refl,
  end }

lemma inner_left_right_apply {A : E →L[𝕜] F} {v : F} {w : E} :
  inner_left_right A v w = ⟪v, A w⟫ := rfl


lemma inner_left_right_map_smul {r : 𝕜} {A : E →L[𝕜] F} {v : F} :
  inner_left_right (r • A) v = r • inner_left_right A v :=
begin
  ext w,
  simp only [inner_smul_right, inner_left_right_apply, algebra.id.smul_eq_mul,
             pi.smul_apply, continuous_linear_map.coe_smul'],
end

lemma inner_left_right_norm (A : E →L[𝕜] F) (v : F) : ∥inner_left_right A v∥ ≤ ∥A∥ * ∥v∥ :=
to_dual_comp_norm A v

--/-- The adjoint, as a bare function. This is only meant as an auxiliary definition for
--the main definition `adjoint`, where this is bundled as a conjugate-linear isometric
--equivalence. -/
--@[simps] def adjoint' (A : E →L[𝕜] F) : F →L[𝕜] E :=
--linear_map.mk_continuous
--{ to_fun := λ v : F, (to_dual 𝕜 E).symm (inner_left_right A v),
--  map_add' := λ x y, by simp only [linear_isometry_equiv.map_add, continuous_linear_map.map_add],
--  map_smul' := λ r x, by simp only [continuous_linear_map.map_smulₛₗ,
--                                    linear_isometry_equiv.map_smulₛₗ,
--                                    star_ring_aut_self_apply r, ring_hom.id_apply,
--                                    ring_equiv.coe_to_ring_hom] }
--∥A∥
--(λ x, by simp only [linear_isometry_equiv.norm_map, inner_left_right_norm, linear_map.coe_mk])
--
--@[simp] lemma adjoint'_apply {A : E →L[𝕜] F} {v : F} :
--  adjoint' A v = (to_dual 𝕜 E).symm (inner_left_right A v) := rfl
--
--def adjoint'' (A : E →L[𝕜] F) :=
--((to_dual 𝕜 E).symm : (normed_space.dual 𝕜 E) →L⋆[𝕜] E).comp (inner_left_right A)
--
--lemma adjoint'_inner_left {A : E →L[𝕜] F} {x : E} {y : F} : ⟪adjoint' A y, x⟫ = ⟪y, A x⟫ :=
--by { simp only [adjoint'_apply, to_dual_symm_inner], refl }
--
--lemma adjoint'_inner_right {A : E →L[𝕜] F} {x : E} {y : F} : ⟪x, adjoint' A y⟫ = ⟪A x, y⟫ :=
--by rw [←inner_conj_sym, adjoint'_inner_left, inner_conj_sym]
--
--lemma adjoint'_adjoint'_apply (A : E →L[𝕜] F) : adjoint' (adjoint' A) = A :=
--begin
--  ext v,
--  refine ext_inner_left 𝕜 (λ w, _),
--  rw [adjoint'_inner_right, adjoint'_inner_left],
--end
--
--lemma adjoint'_norm {A : E →L[𝕜] F} : ∥adjoint' A∥ = ∥A∥ :=
--begin
--  refine le_antisymm _ _,
--  { refine continuous_linear_map.op_norm_le_bound _ (norm_nonneg _) (λ x, _),
--    rw [adjoint'_apply, linear_isometry_equiv.norm_map],
--    exact inner_left_right_norm _ _ },
--  { nth_rewrite_lhs 0 [←adjoint'_adjoint'_apply A],
--    refine continuous_linear_map.op_norm_le_bound _ (norm_nonneg _) (λ x, _),
--    rw [adjoint'_apply, linear_isometry_equiv.norm_map],
--    exact inner_left_right_norm _ _ }
--end
--
--/-- The adjoint of a bounded operator from Hilbert space E to Hilbert space F. -/
--def adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] E) :=
--linear_isometry_equiv.of_surjective
--{ to_fun := adjoint',
--  map_add' := λ A B,
--  begin
--    ext v,
--    simp only [adjoint'_apply, continuous_linear_map.add_apply,
--              ←linear_isometry_equiv.map_add, linear_isometry_equiv.map_eq_iff],
--    ext w,
--    simp only [inner_add_right, inner_left_right_apply, continuous_linear_map.add_apply],
--  end,
--  map_smul' := λ r A,
--  begin
--    ext v,
--    simp only [adjoint'_apply, inner_left_right_map_smul, linear_isometry_equiv.map_smulₛₗ,
--               ring_equiv.coe_to_ring_hom, continuous_linear_map.coe_smul', pi.smul_apply],
--  end,
--  norm_map' := λ A, adjoint'_norm }
--(λ A, ⟨adjoint' A, adjoint'_adjoint'_apply A⟩)

def adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] E) :=
linear_isometry_equiv.of_surjective
{ to_fun := λ A, ((to_dual 𝕜 E).symm : (normed_space.dual 𝕜 E) →L⋆[𝕜] E).comp (inner_left_right A),
  map_add' := λ A B, by simp [add_monoid_hom.comp_add],
  map_smul' := λ r A,
  begin
    ext v,
    simp [inner_left_right_map_smul],
  end,
  norm_map' := λ A, begin
    sorry
  end }
sorry
--(λ A, ⟨adjoint' A, adjoint'_adjoint'_apply A⟩)

/-- The fundamental property of the adjoint. -/
lemma adjoint_inner_left {A : E →L[𝕜] F} {x : E} {y : F} : ⟪adjoint A y, x⟫ = ⟪y, A x⟫ :=
--adjoint'_inner_left
sorry

/-- The fundamental property of the adjoint. -/
lemma adjoint_inner_right {A : E →L[𝕜] F} {x : E} {y : F} : ⟪x, adjoint A y⟫ = ⟪A x, y⟫ :=
--adjoint'_inner_right
sorry

/-- The adjoint is involutive -/
@[simp] lemma adjoint_adjoint_apply {A : E →L[𝕜] F} : adjoint (adjoint A) = A :=
--adjoint'_adjoint'_apply A
sorry

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

--def adjoint_equiv (A : E ≃L[𝕜] F) : (F ≃L[𝕜] E) := sorry

end inner_product_space
