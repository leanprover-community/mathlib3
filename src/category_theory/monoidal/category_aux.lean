/-
-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Michael Jendrusch, Scott Morrison
--
-- Auxiliary definitions for the definition of a monoidal category.
-/
import category_theory.products

universes v u

open category_theory

namespace category_theory.monoidal_category_aux

@[reducible] def tensor_obj_type
  (C : Sort u) [category.{v} C] :=
C → C → C

@[reducible] def tensor_hom_type
  {C : Sort u} [category.{v} C] (tensor_obj : tensor_obj_type C) : Sort (imax u u u u v) :=
Π {X₁ Y₁ X₂ Y₂ : C}, (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → ((tensor_obj X₁ X₂) ⟶ (tensor_obj Y₁ Y₂))

def assoc_obj
  {C : Sort u} [category.{v} C] (tensor_obj : tensor_obj_type C) : Sort (max u v 1) :=
Π X Y Z : C, (tensor_obj (tensor_obj X Y) Z) ≅ (tensor_obj X (tensor_obj Y Z))

def assoc_natural
  {C : Sort u} [category.{v} C]
  (tensor_obj : tensor_obj_type C)
  (tensor_hom : tensor_hom_type tensor_obj)
  (assoc : assoc_obj tensor_obj) : Prop :=
∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
  (tensor_hom (tensor_hom f₁ f₂) f₃) ≫ (assoc Y₁ Y₂ Y₃).hom = (assoc X₁ X₂ X₃).hom ≫ (tensor_hom f₁ (tensor_hom f₂ f₃))

def left_unitor_obj
  {C : Sort u} [category.{v} C]
  (tensor_obj : tensor_obj_type C)
  (tensor_unit : C) : Sort (max v 1 u) :=
Π X : C, (tensor_obj tensor_unit X) ≅ X

def left_unitor_natural
  {C : Sort u} [category.{v} C]
  (tensor_obj : tensor_obj_type C)
  (tensor_hom : tensor_hom_type tensor_obj)
  (tensor_unit : C)
  (left_unitor : left_unitor_obj tensor_obj tensor_unit) : Prop :=
∀ {X Y : C} (f : X ⟶ Y),
  (tensor_hom (𝟙 tensor_unit) f) ≫ (left_unitor Y).hom = (left_unitor X).hom ≫ f

def right_unitor_obj
  {C : Sort u} [category.{v} C]
  (tensor_obj : tensor_obj_type C)
  (tensor_unit : C) : Sort (max v 1 u) :=
Π (X : C), (tensor_obj X tensor_unit) ≅ X

def right_unitor_natural
  {C : Sort u} [category.{v} C]
  (tensor_obj : tensor_obj_type C)
  (tensor_hom : tensor_hom_type tensor_obj)
  (tensor_unit : C)
  (right_unitor : right_unitor_obj tensor_obj tensor_unit) : Prop :=
∀ {X Y : C} (f : X ⟶ Y),
  (tensor_hom f (𝟙 tensor_unit)) ≫ (right_unitor Y).hom = (right_unitor X).hom ≫ f

@[reducible] def pentagon
  {C : Sort u} [category.{v} C]
  {tensor_obj : tensor_obj_type C}
  (tensor_hom : tensor_hom_type tensor_obj)
  (assoc : assoc_obj tensor_obj) : Prop :=
∀ W X Y Z : C,
  (tensor_hom (assoc W X Y).hom (𝟙 Z)) ≫ (assoc W (tensor_obj X Y) Z).hom ≫ (tensor_hom (𝟙 W) (assoc X Y Z).hom)
  = (assoc (tensor_obj W X) Y Z).hom ≫ (assoc W X (tensor_obj Y Z)).hom

@[reducible] def triangle
  {C : Sort u} [category.{v} C]
  {tensor_obj : tensor_obj_type C} {tensor_unit : C}
  (tensor_hom : tensor_hom_type tensor_obj)
  (left_unitor : left_unitor_obj tensor_obj tensor_unit)
  (right_unitor : right_unitor_obj tensor_obj tensor_unit)
  (assoc : assoc_obj tensor_obj) : Prop :=
∀ X Y : C,
  (assoc X tensor_unit Y).hom ≫ (tensor_hom (𝟙 X) (left_unitor Y).hom)
  = tensor_hom (right_unitor X).hom (𝟙 Y)

end category_theory.monoidal_category_aux
