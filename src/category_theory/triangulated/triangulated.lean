/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.triangulated.pretriangulated

/-!
# Triangulated Categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition of triangulated categories, which are
pretriangulated categories which satisfy the octahedron axiom.

-/

noncomputable theory

namespace category_theory

open limits category preadditive pretriangulated
open_locale zero_object

variables {C : Type*} [category C] [preadditive C] [has_zero_object C] [has_shift C ℤ]
  [∀ (n : ℤ), functor.additive (shift_functor C n)] [pretriangulated C]

variables {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C} {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃}
  (comm : u₁₂ ≫ u₂₃ = u₁₃)
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₂ : triangle.mk u₁₂ v₁₂ w₁₂ ∈ dist_triang C)
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} (h₂₃ : triangle.mk u₂₃ v₂₃ w₂₃ ∈ dist_triang C)
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₃ : triangle.mk u₁₃ v₁₃ w₁₃ ∈ dist_triang C)

namespace triangulated

include comm h₁₂ h₂₃ h₁₃

/-- An octahedron is a type of datum whose existence is asserted by
the octahedron axiom (TR 4), see https://stacks.math.columbia.edu/tag/05QK -/
structure octahedron :=
(m₁ : Z₁₂ ⟶ Z₁₃)
(m₃ : Z₁₃ ⟶ Z₂₃)
(comm₁ : v₁₂ ≫ m₁ = u₂₃ ≫ v₁₃)
(comm₂ : m₁ ≫ w₁₃ = w₁₂)
(comm₃ : v₁₃ ≫ m₃ = v₂₃)
(comm₄ : w₁₃ ≫ u₁₂⟦1⟧' = m₃ ≫ w₂₃)
(mem : triangle.mk m₁ m₃ (w₂₃ ≫ v₁₂⟦1⟧') ∈ dist_triang C)

omit comm h₁₂ h₂₃ h₁₃

instance (X : C) : nonempty (octahedron (comp_id (𝟙 X)) (contractible_distinguished X)
  (contractible_distinguished X) (contractible_distinguished X)) :=
begin
  refine ⟨⟨0, 0, _, _, _, _, by convert contractible_distinguished (0 : C)⟩⟩,
  all_goals { apply subsingleton.elim, },
end

namespace octahedron

attribute [reassoc] comm₁ comm₂ comm₃ comm₄

variables {comm h₁₂ h₂₃ h₁₃} (h : octahedron comm h₁₂ h₂₃ h₁₃)

/-- The triangle `Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃ ⟶ Z₁₂⟦1⟧` given by an octahedron. -/
@[simps]
def triangle : triangle C := triangle.mk h.m₁ h.m₃ (w₂₃ ≫ v₁₂⟦1⟧')

/-- The first morphism of triangles given by an octahedron. -/
@[simps]
def triangle_morphism₁ : triangle.mk u₁₂ v₁₂ w₁₂ ⟶ triangle.mk u₁₃ v₁₃ w₁₃ :=
{ hom₁ := 𝟙 X₁,
  hom₂ := u₂₃,
  hom₃ := h.m₁,
  comm₁' := by { dsimp, rw [id_comp, comm], },
  comm₂' := h.comm₁,
  comm₃' := by { dsimp, simpa only [functor.map_id, comp_id] using h.comm₂.symm, }, }

/-- The second morphism of triangles given an octahedron. -/
@[simps]
def triangle_morphism₂ : triangle.mk u₁₃ v₁₃ w₁₃ ⟶ triangle.mk u₂₃ v₂₃ w₂₃ :=
{ hom₁ := u₁₂,
  hom₂ := 𝟙 X₃,
  hom₃ := h.m₃,
  comm₁' := by { dsimp, rw [comp_id, comm], },
  comm₂' := by { dsimp, rw [id_comp, h.comm₃], },
  comm₃' := h.comm₄, }

/- TODO (@joelriou): show that in order to verify the existence of an octahedron, one may
replace the composable maps `u₁₂` and `u₂₃` by any isomorphic composable maps
and the given "cones" of `u₁₂`, `u₂₃`, `u₁₃` by any choice of cones. -/

end octahedron

end triangulated

open triangulated

variable (C)

/-- A triangulated category is a pretriangulated category which satisfies
the octahedron axiom (TR 4), see https://stacks.math.columbia.edu/tag/05QK -/
class is_triangulated :=
(octahedron_axiom : ∀ ⦃X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C⦄ ⦃u₁₂ : X₁ ⟶ X₂⦄ ⦃u₂₃ : X₂ ⟶ X₃⦄ ⦃u₁₃ : X₁ ⟶ X₃⦄
  (comm : u₁₂ ≫ u₂₃ = u₁₃)
  ⦃v₁₂ : X₂ ⟶ Z₁₂⦄ ⦃w₁₂ : Z₁₂ ⟶ X₁⟦1⟧⦄ (h₁₂ : triangle.mk u₁₂ v₁₂ w₁₂ ∈ dist_triang C)
  ⦃v₂₃ : X₃ ⟶ Z₂₃⦄ ⦃w₂₃ : Z₂₃ ⟶ X₂⟦1⟧⦄ (h₂₃ : triangle.mk u₂₃ v₂₃ w₂₃ ∈ dist_triang C)
  ⦃v₁₃ : X₃ ⟶ Z₁₃⦄ ⦃w₁₃ : Z₁₃ ⟶ X₁⟦1⟧⦄ (h₁₃ : triangle.mk u₁₃ v₁₃ w₁₃ ∈ dist_triang C),
  nonempty (octahedron comm h₁₂ h₂₃ h₁₃))

namespace triangulated

variable {C}

/-- A choice of octahedron given by the octahedron axiom. -/
def some_octahedron [is_triangulated C] : octahedron comm h₁₂ h₂₃ h₁₃ :=
(is_triangulated.octahedron_axiom comm h₁₂ h₂₃ h₁₃).some

end triangulated

end category_theory
