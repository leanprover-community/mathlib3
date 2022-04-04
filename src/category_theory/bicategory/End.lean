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
  associator_naturality' := begin
    intros,
    rw category.assoc, rw associator_naturality_right,
    rw bicategory.whisker_right_comp,
    slice_lhs 2 3 { rw associator_naturality_middle, },
    slice_lhs 1 2 { rw associator_naturality_left, },
    rw bicategory.whisker_left_comp,
    simp only [category.assoc],
  end,
  left_unitor_naturality' := begin
    intros,
    rw [bicategory.whisker_right_id, category.id_comp, bicategory.left_unitor_naturality],
  end,
  right_unitor_naturality' := begin
    intros,
    rw [bicategory.whisker_left_id, category.comp_id, bicategory.right_unitor_naturality],
  end,
  pentagon' := begin
    intros,
    simp only [bicategory.whisker_left_id, bicategory.whisker_right_id, category.id_comp,
      category.comp_id, bicategory.pentagon],
  end, }

end category_theory
