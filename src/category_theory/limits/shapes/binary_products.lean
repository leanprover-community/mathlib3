-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.shapes.products

universes v u

open category_theory

namespace category_theory.limits

@[derive decidable_eq] inductive walking_pair : Type v
| left | right

def pair {C : Sort u} (X Y : C) : walking_pair → C
| walking_pair.left := X
| walking_pair.right := Y

variables {C : Sort u} [𝒞 : category.{v+1} C]
include 𝒞

variables {X Y : C}

def binary_fan {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : fan (pair X Y) :=
{ X := P,
  π := { app := λ j, walking_pair.cases_on j π₁ π₂ }}
def binary_cofan {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : cofan (pair X Y) :=
{ X := P,
  ι := { app := λ j, walking_pair.cases_on j ι₁ ι₂ }}

def fan.π₁ {f : walking_pair → C} (t : fan f) : t.X ⟶ f walking_pair.left :=
t.π.app walking_pair.left
def fan.π₂ {f : walking_pair → C} (t : fan f) : t.X ⟶ f walking_pair.right :=
t.π.app walking_pair.right

def cofan.ι₁ {f : walking_pair → C} (t : cofan f) : f walking_pair.left ⟶ t.X :=
t.ι.app walking_pair.left
def cofan.ι₂ {f : walking_pair → C} (t : cofan f) : f walking_pair.right ⟶ t.X :=
t.ι.app walking_pair.right

end category_theory.limits
