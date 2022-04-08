/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.bicategory.basic
import category_theory.monoidal.category

/-!
# Endomorphisms of an object in a bicategory, as a monoidal category.
-/

namespace category_theory

variables {C : Type*} [bicategory C]

/-- The endomorphisms of an object in a bicategory can be considered as a monoidal category. -/
@[derive category]
def End_monoidal (X : C) := X ⟶ X

instance (X : C) : inhabited (End_monoidal X) := ⟨𝟙 X⟩

open_locale bicategory

open monoidal_category
open bicategory

instance (X : C) : monoidal_category (End_monoidal X) :=
{ tensor_obj := λ X Y, X ≫ Y,
  tensor_hom := λ W X Y Z f g, (f ▷ Y) ≫ (X ◁ g),
  tensor_unit := 𝟙 _,
  associator := λ X Y Z, α_ X Y Z,
  left_unitor := λ X, λ_ X,
  right_unitor := λ X, ρ_ X,
  tensor_comp' := λ X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂,
    by rw [bicategory.whisker_left_comp, bicategory.comp_whisker_right, category.assoc,
      category.assoc, bicategory.whisker_exchange_assoc], }

end category_theory
