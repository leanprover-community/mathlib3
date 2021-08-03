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

notation X `^*`:1200 := dual X
notation `η_`:100 X := @coevaluation _ _ _ X _
notation `ε_`:100 X := @has_right_dual.evaluation _ _ _ X _

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

def adjoint_mate {X Y : C} [has_right_dual X] [has_right_dual Y] (f : X ⟶ Y) : Y^* ⟶ X^* :=
(ρ_ _).inv ≫ (𝟙 Y^* ⊗ η_ X)
  ≫ (𝟙 (Y^*) ⊗ (f ⊗ 𝟙 X^*))
  ≫ (α_ _ _ _).inv
  ≫ ((ε_ _) ⊗ 𝟙 _)
  ≫ (λ_ _).hom

theorem adjoint_mate_id {X : C} [has_right_dual X] : adjoint_mate (𝟙 X) = 𝟙 X^* :=
begin
  unfold adjoint_mate,
  simp only [monoidal_category.tensor_id, category.id_comp],
  sorry
end

def has_right_dual_dual_tensor (X Y : C) [hX : has_right_dual X] [hY : has_right_dual Y]
: has_right_dual (X ⊗ Y) :=
{ dual := Y ^* ⊗ X ^*,
  coevaluation := (η_ _) ≫ (𝟙 _ ⊗ ((λ_ _).inv ≫ ((η_ _) ⊗ 𝟙 _) ≫ (α_ _ _ _).hom)) ≫ (α_ _ _ _).inv,
  evaluation := (α_ _ _ _).hom ≫ (𝟙 _ ⊗ ((α_ _ _ _).inv ≫ ((ε_ _) ⊗ 𝟙 Y) ≫ (λ_ Y).hom)) ≫ ε_ _,
  evaluation_coevaluation' := by { sorry },
  coevaluation_evaluation' := by sorry }

/- A right rigid monoidal category is one in which every object has a right dual. -/
class right_rigid_category (C : Type u) [category.{v} C] [monoidal_category.{v} C] :=
  (dual : Π (X : C), has_right_dual X)

attribute [instance] right_rigid_category.dual

end category_theory
