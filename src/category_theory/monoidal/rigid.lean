/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/

import category_theory.monoidal.category

open category_theory

universes v v₁ v₂ v₃ u u₁ u₂ u₃
noncomputable theory

namespace category_theory

variables {C : Type u₁} [category.{v₁} C] [monoidal_category C]

/- A right dual of an object `X : C` is ... -/
class has_right_dual (X : C) :=
  (dual : C)
  (coevaluation : 𝟙_ C ⟶ X ⊗ dual)
  (evaluation : dual ⊗ X ⟶ 𝟙_ C)
  (coevaluation_evaluation' :
    (ρ_ dual).hom ≫ (λ_ dual).inv
    = (𝟙 dual ⊗ coevaluation) ≫ (α_ _ _ _).inv ≫ (evaluation ⊗ 𝟙 dual)
    . obviously)
  (evaluation_coevaluation' :
    (λ_ X).hom ≫ (ρ_ X).inv
    = (coevaluation ⊗ 𝟙 X) ≫ (α_ _ _ _).hom ≫ (𝟙 X ⊗ evaluation)
    . obviously)

open has_right_dual

restate_axiom coevaluation_evaluation'
restate_axiom evaluation_coevaluation'

notation X ` ^*`:120 := dual X
notation `η_` := coevaluation
notation `ε_` := evaluation

def has_right_dual_unit : has_right_dual (𝟙_ C) :=
{ dual := 𝟙_C,
  coevaluation := (ρ_ _).inv,
  evaluation := (ρ_ _).hom,
  coevaluation_evaluation' := by {
    rw[monoidal_category.triangle_assoc_comp_right,
      monoidal_category.unitors_inv_equal,
      monoidal_category.unitors_equal], simp },
  evaluation_coevaluation' := by {
    rw[monoidal_category.triangle_assoc_comp_right_inv_assoc,
      monoidal_category.unitors_inv_equal,
      monoidal_category.unitors_equal], simp } }


/- A right rigid monoidal category is one in which every object has a right dual. -/
class right_rigid_category (C : Type u) [category.{v} C] [monoidal_category.{v} C] :=
  (dual : Π (X : C), has_right_dual X)

attribute [instance] right_rigid_category.dual

end category_theory
