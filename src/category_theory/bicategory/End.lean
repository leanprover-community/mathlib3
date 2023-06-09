/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.bicategory.basic
import category_theory.monoidal.category

/-!
# Endomorphisms of an object in a bicategory, as a monoidal category.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
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
{ tensor_obj := λ f g, f ≫ g,
  tensor_hom := λ f g h i η θ, (η ▷ h) ≫ (g ◁ θ),
  tensor_unit := 𝟙 _,
  associator := λ f g h, α_ f g h,
  left_unitor := λ f, λ_ f,
  right_unitor := λ f, ρ_ f,
  tensor_comp' := begin
    intros,
    rw [bicategory.whisker_left_comp, bicategory.comp_whisker_right, category.assoc, category.assoc,
      bicategory.whisker_exchange_assoc],
  end }

end category_theory
