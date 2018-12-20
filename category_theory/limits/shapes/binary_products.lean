-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.shapes.products

universes u v

open category_theory

namespace category_theory.limits

@[derive decidable_eq] inductive two : Type v
| left | right

def two.map {C : Type u} (X Y : C) : two → C
| two.left := X
| two.right := Y

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

variables {X Y : C}

def binary_fan {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : fan (two.map X Y) :=
{ X := P,
  π := { app := λ j, two.cases_on j π₁ π₂ }}
def binary_cofan {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : cofan (two.map X Y) :=
{ X := P,
  ι := { app := λ j, two.cases_on j ι₁ ι₂ }}

def fan.π₁ {f : two → C} (t : fan f) : t.X ⟶ f two.left := t.π.app two.left
def fan.π₂ {f : two → C} (t : fan f) : t.X ⟶ f two.right := t.π.app two.right

def cofan.ι₁ {f : two → C} (t : cofan f) : f two.left ⟶ t.X := t.ι.app two.left
def cofan.ι₂ {f : two → C} (t : cofan f) : f two.right ⟶ t.X := t.ι.app two.right

end category_theory.limits
