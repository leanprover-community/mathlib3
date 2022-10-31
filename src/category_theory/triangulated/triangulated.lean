/-
Copyright (c) 2022 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.triangulated.pretriangulated

/-!
# Triangulated Categories

This file contains the definition of triangulated categories, which are
pretriangulated categories which satisfy the octahedron axiom.

-/

noncomputable theory

namespace category_theory

open limits category preadditive pretriangulated
open_locale zero_object

variables {C : Type*} [category C] [preadditive C] [has_zero_object C] [has_shift C ℤ]
  [∀ (n : ℤ), functor.additive (shift_functor C n)] [pretriangulated C]

namespace triangulated

variables {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C} {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃}
  (comm : u₁₂ ≫ u₂₃ = u₁₃)
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₂ : triangle.mk u₁₂ v₁₂ w₁₂ ∈ dist_triang C)
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} (h₂₃ : triangle.mk u₂₃ v₂₃ w₂₃ ∈ dist_triang C)
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₃ : triangle.mk u₁₃ v₁₃ w₁₃ ∈ dist_triang C)

include comm h₁₂ h₂₃ h₁₃

/-- The octahedron axiom (TR 4), see https://stacks.math.columbia.edu/tag/05QK -/
@[nolint unused_arguments]
def octahedron_exists : Prop :=
∃ (m₁ : Z₁₂ ⟶ Z₁₃) (m₃ : Z₁₃ ⟶ Z₂₃) (comm₁ : v₁₂ ≫ m₁ = u₂₃ ≫ v₁₃)
    (comm₂ : w₁₂ = m₁ ≫ w₁₃) (comm₃ : v₁₃ ≫ m₃ = v₂₃) (comm₄ : w₁₃ ≫ u₁₂⟦1⟧' = m₃ ≫ w₂₃),
    triangle.mk m₁ m₃ (w₂₃ ≫ v₁₂⟦1⟧') ∈ dist_triang C

omit comm h₁₂ h₂₃ h₁₃

namespace octahedron_exists

variables {comm h₁₂ h₂₃ h₁₃} (h : octahedron_exists comm h₁₂ h₂₃ h₁₃)

/-- A choice of morphism `m₁ : Z₁₂ ⟶ Z₁₃` for the octahedron axiom. -/
def m₁ : Z₁₂ ⟶ Z₁₃ := h.some

/-- A choice of morphism `m₃ : Z₁₃ ⟶ Z₂₃` for the octahedron axiom. -/
def m₃ : Z₁₃ ⟶ Z₂₃ := h.some_spec.some

/-- The triangle `Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃ ⟶ Z₁₂⟦1⟧` given by the octahedron axiom. -/
@[simps]
def triangle : triangle C := triangle.mk h.m₁ h.m₃ (w₂₃ ≫ v₁₂⟦1⟧')

/-- The triangle `Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃ ⟶ Z₁₂⟦1⟧` given by the octahedron axiom
is distringuished. -/
lemma mem_dist_triang : h.triangle ∈ dist_triang C :=
h.some_spec.some_spec.some_spec.some_spec.some_spec.some_spec

/-- The first morphism of triangles asserted by the octahedron axiom. -/
@[simps]
def triangle_morphism₁ : triangle.mk u₁₂ v₁₂ w₁₂ ⟶ triangle.mk u₁₃ v₁₃ w₁₃ :=
{ hom₁ := 𝟙 X₁,
  hom₂ := u₂₃,
  hom₃ := h.m₁,
  comm₁' := by { dsimp, rw [id_comp, comm], },
  comm₂' := h.some_spec.some_spec.some,
  comm₃' := begin
    dsimp,
    simpa only [functor.map_id, comp_id]
      using h.some_spec.some_spec.some_spec.some,
  end }

/-- The second morphism of triangles asserted by the octahedron axiom. -/
@[simps]
def triangle_morphism₂ : triangle.mk u₁₃ v₁₃ w₁₃ ⟶ triangle.mk u₂₃ v₂₃ w₂₃ :=
{ hom₁ := u₁₂,
  hom₂ := 𝟙 X₃,
  hom₃ := h.m₃,
  comm₁' := by { dsimp, rw [comp_id, comm], },
  comm₂' := begin
    dsimp,
    simpa only [id_comp] using
      h.some_spec.some_spec.some_spec.some_spec.some,
  end,
  comm₃' := h.some_spec.some_spec.some_spec.some_spec.some_spec.some, }

/- TODO (@joelriou): show that in order to verify the octahedron axiom, one may
replace the composable maps `u₁₂` and `u₂₃` by any isomorphic composable maps
and the given "cones" of `u₁₂`, `u₂₃`, `u₁₃` by any choice of cones. -/

end octahedron_exists

end triangulated

open triangulated

variable (C)

/-- A triangulated category is a pretriangulated which satisfies the octahedron axiom. -/
class triangulated :=
(octahedron' : ∀ ⦃X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C⦄ ⦃u₁₂ : X₁ ⟶ X₂⦄ ⦃u₂₃ : X₂ ⟶ X₃⦄ ⦃u₁₃ : X₁ ⟶ X₃⦄
  (comm : u₁₂ ≫ u₂₃ = u₁₃)
  ⦃v₁₂ : X₂ ⟶ Z₁₂⦄ ⦃w₁₂ : Z₁₂ ⟶ X₁⟦1⟧⦄ (h₁₂ : triangle.mk u₁₂ v₁₂ w₁₂ ∈ dist_triang C)
  ⦃v₂₃ : X₃ ⟶ Z₂₃⦄ ⦃w₂₃ : Z₂₃ ⟶ X₂⟦1⟧⦄ (h₂₃ : triangle.mk u₂₃ v₂₃ w₂₃ ∈ dist_triang C)
  ⦃v₁₃ : X₃ ⟶ Z₁₃⦄ ⦃w₁₃ : Z₁₃ ⟶ X₁⟦1⟧⦄ (h₁₃ : triangle.mk u₁₃ v₁₃ w₁₃ ∈ dist_triang C),
  triangulated.octahedron_exists comm h₁₂ h₂₃ h₁₃)

end category_theory
