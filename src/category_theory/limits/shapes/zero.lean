/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.terminal

universes v u

open category_theory

namespace category_theory.limits

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

class has_zero_object :=
(zero : C)
(unique_to : ∀ X : C, unique (zero ⟶ X))
(unique_from : ∀ X : C, unique (X ⟶ zero))

variables [has_zero_object.{v} C]

variables {C}

instance [has_zero_object.{v} C] : has_zero C :=
{ zero := has_zero_object.zero.{v} C }

instance unique_from (X : C) : unique (X ⟶ 0) := has_zero_object.unique_from.{v} X
instance unique_to (X : C) : unique (0 ⟶ X) := has_zero_object.unique_to.{v} X

def zero_morphism (X Y : C) :=
inhabited.default (X ⟶ 0) ≫ inhabited.default (0 ⟶ Y)

instance hom_has_zero {X Y : C} : has_zero (X ⟶ Y) :=
{ zero := zero_morphism X Y }

@[simp, reassoc] lemma zero_morphism_comp {X Y Z : C} (f : Y ⟶ Z) : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) :=
by { dsimp [has_zero.zero, zero_morphism], rw [category.assoc], congr, }
@[simp] lemma comp_zero_morphism {X Y Z : C} (f : X ⟶ Y) : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) :=
by { dsimp [has_zero.zero, zero_morphism], rw [←category.assoc], congr, }

instance has_initial_of_has_zero : has_initial.{v} C :=
has_initial_of_unique 0
instance has_terminal_of_has_zero : has_terminal.{v} C :=
has_terminal_of_unique 0

end category_theory.limits
