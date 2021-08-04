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

/- An exact pairing is a pair of objects `X Y : C` which admit
  a coevaluation and evaluation morphism which fulfill two triangle equalities. -/
class exact_pairing (X Y : C) :=
  (coevaluation [] : 𝟙_ C ⟶ X ⊗ Y)
  (evaluation [] : Y ⊗ X ⟶ 𝟙_ C)
  (coevaluation_evaluation' :
    (𝟙 Y ⊗ coevaluation) ≫ (α_ _ _ _).inv ≫ (evaluation ⊗ 𝟙 Y)
    = (ρ_ Y).hom ≫ (λ_ Y).inv . obviously)
  (evaluation_coevaluation' :
    (coevaluation ⊗ 𝟙 X) ≫ (α_ _ _ _).hom ≫ (𝟙 X ⊗ evaluation)
    = (λ_ X).hom ≫ (ρ_ X).inv . obviously)

open exact_pairing

notation `η_` := exact_pairing.coevaluation
notation `ε_` := exact_pairing.evaluation

restate_axiom coevaluation_evaluation'
attribute [reassoc, simp] exact_pairing.coevaluation_evaluation
restate_axiom evaluation_coevaluation'
attribute [reassoc, simp] exact_pairing.evaluation_coevaluation

instance exact_pairing_unit : exact_pairing (𝟙_ C) (𝟙_ C) :=
{ coevaluation := (ρ_ _).inv,
  evaluation := (ρ_ _).hom,
  coevaluation_evaluation' := by {
    rw[monoidal_category.triangle_assoc_comp_right,
      monoidal_category.unitors_inv_equal,
      monoidal_category.unitors_equal], simp },
  evaluation_coevaluation' := by {
    rw[monoidal_category.triangle_assoc_comp_right_inv_assoc,
      monoidal_category.unitors_inv_equal,
      monoidal_category.unitors_equal], simp } }

/- A class of objects which have a right dual, -/
class has_right_dual (X : C) :=
  (right_dual : C)
  [exact : exact_pairing X right_dual]

/- ... and a class of objects with have a left dual.-/
class has_left_dual (Y : C) :=
  (left_dual : C)
  [exact : exact_pairing left_dual Y]

attribute [instance] has_right_dual.exact
attribute [instance] has_left_dual.exact

open exact_pairing has_right_dual has_left_dual

notation X `^*`:1200 := right_dual X
notation `*^`:1200 X := left_dual X


def has_right_dual_unit : has_right_dual (𝟙_ C) :=
{ right_dual := 𝟙_ C }

def has_left_dual_unit : has_left_dual (𝟙_ C) :=
{ left_dual := 𝟙_ C }

def right_adjoint_mate {X Y : C} [has_right_dual X] [has_right_dual Y] (f : X ⟶ Y) : Y^* ⟶ X^* :=
(ρ_ _).inv ≫ (𝟙 Y^* ⊗ η_ _ _)
  ≫ (𝟙 (Y^*) ⊗ (f ⊗ 𝟙 X^*))
  ≫ (α_ _ _ _).inv
  ≫ ((ε_ _ _) ⊗ 𝟙 _)
  ≫ (λ_ _).hom

notation f `^*`:1200 := right_adjoint_mate f

@[simp] --Do we want this to be simp?
theorem right_adjoint_mate_id {X : C} [has_right_dual X] : (𝟙 X)^* = 𝟙 X^* :=
begin
  simp only [right_adjoint_mate, monoidal_category.tensor_id, category.id_comp],
  slice_lhs 2 4 { rw coevaluation_evaluation },
  simp
end

theorem right_adjoint_mate_comp {X Y Z : C}
  [has_right_dual X] [has_right_dual Y] [has_right_dual Z] {f : X ⟶ Y} {g : Y ⟶ Z} :
  right_adjoint_mate (f ≫ g) = right_adjoint_mate g ≫ right_adjoint_mate f :=
begin
  simp only [right_adjoint_mate],
  simp only [monoidal_category.id_tensor_comp,
    monoidal_category.comp_tensor_id, iso.cancel_iso_inv_left, category.assoc],
  --slice_rhs 5 6 { rw ←coevaluation_evaluation },
  sorry
end

/- A right rigid monoidal category is one in which every object has a right dual. -/
class right_rigid_category (C : Type u) [category.{v} C] [monoidal_category.{v} C] :=
  (dual : Π (X : C), has_right_dual X)

attribute [instance] right_rigid_category.dual

end category_theory
