/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.zero
import category_theory.shift

/-!
# Differential objects in a category.

A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : X ⟶ X⟦1⟧`, such that `d^2 = 0`.

We build the category of differential objects, and some basic constructions
such as the forgetful functor, and zero morphisms and zero objects.
-/

open category_theory.limits

universes v u

namespace category_theory

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

variables [has_zero_morphisms.{v} C] [has_shift.{v} C]

/--
A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : X ⟶ X⟦1⟧`, such that `d^2 = 0`.
-/
@[nolint has_inhabited_instance]
structure differential_object :=
(X : C)
(d : X ⟶ X⟦1⟧)
(d_squared' : d ≫ d⟦1⟧' = 0 . obviously)

restate_axiom differential_object.d_squared'
attribute [simp] differential_object.d_squared

variables {C}

namespace differential_object

/--
A morphism of differential objects is a morphism commuting with the differentials.
-/
@[ext, nolint has_inhabited_instance]
structure hom (X Y : differential_object.{v} C) :=
(f : X.X ⟶ Y.X)
(comm' : X.d ≫ f⟦1⟧' = f ≫ Y.d . obviously)

restate_axiom hom.comm'
attribute [simp, reassoc] hom.comm

namespace hom

/-- The identity morphism of a differential object. -/
@[simps]
def id (X : differential_object.{v} C) : hom X X :=
{ f := 𝟙 X.X }

/-- The composition of morphisms of differential objects. -/
@[simps]
def comp {X Y Z : differential_object.{v} C} (f : hom X Y) (g : hom Y Z) : hom X Z :=
{ f := f.f ≫ g.f, }

end hom

instance category_of_differential_objects : category.{v} (differential_object.{v} C) :=
{ hom := hom,
  id := hom.id,
  comp := λ X Y Z f g, hom.comp f g, }

@[simp]
lemma id_f (X : differential_object.{v} C) : ((𝟙 X) : X ⟶ X).f = 𝟙 (X.X) := rfl

@[simp]
lemma comp_f {X Y Z : differential_object.{v} C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).f = f.f ≫ g.f :=
rfl

variables (C)

/-- The forgetful functor taking a differential object to its underlying object. -/
def forget : (differential_object.{v} C) ⥤ C :=
{ obj := λ X, X.X,
  map := λ X Y f, f.f, }

instance forget_faithful : faithful (forget C) :=
{ }

instance has_zero_morphisms : has_zero_morphisms.{v} (differential_object.{v} C) :=
{ has_zero := λ X Y,
  ⟨{ f := 0, }⟩}

variables {C}

@[simp]
lemma zero_f (P Q : differential_object.{v} C) : (0 : P ⟶ Q).f = 0 := rfl

end differential_object

end category_theory

namespace category_theory

namespace differential_object

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

variables [has_zero_object.{v} C] [has_zero_morphisms.{v} C] [has_shift.{v} C]

local attribute [instance] has_zero_object.has_zero

instance has_zero_object : has_zero_object.{v} (differential_object.{v} C) :=
{ zero :=
  { X := (0 : C),
    d := 0, },
  unique_to := λ X, ⟨⟨{ f := 0 }⟩, λ f, (by ext)⟩,
  unique_from := λ X, ⟨⟨{ f := 0 }⟩, λ f, (by ext)⟩, }

end differential_object

namespace differential_object

variables (C : Type (u+1)) [large_category C] [𝒞 : concrete_category C]
  [has_zero_morphisms.{u} C] [has_shift.{u} C]
include 𝒞

instance concrete_category_of_differential_objects :
  concrete_category (differential_object.{u} C) :=
{ forget := forget C ⋙ category_theory.forget C }

instance : has_forget₂ (differential_object.{u} C) C :=
{ forget₂ := forget C }

end differential_object

end category_theory
