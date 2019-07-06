-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.cones
import category_theory.discrete_category

universes v u

open category_theory

namespace category_theory.limits

@[derive decidable_eq] inductive walking_pair : Type v
| left | right

def pair_function {C : Type u} (X Y : C) : walking_pair → C
| walking_pair.left := X
| walking_pair.right := Y

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞

def pair (X Y : C) : discrete walking_pair ⥤ C :=
functor.of_function (pair_function X Y)

abbreviation binary_fan (X Y : C) := cone (pair X Y)
abbreviation binary_cofan (X Y : C) := cocone (pair X Y)

variables {X Y : C}

def binary_fan.mk {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : binary_fan X Y :=
{ X := P,
  π := { app := λ j, walking_pair.cases_on j π₁ π₂ }}
def binary_cofan.mk {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : binary_cofan X Y :=
{ X := P,
  ι := { app := λ j, walking_pair.cases_on j ι₁ ι₂ }}

end category_theory.limits
