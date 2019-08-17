/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.terminal
import category_theory.discrete_category

universes v u

open category_theory

namespace category_theory.limits

@[derive decidable_eq]
inductive walking_pair : Type v
| left | right

instance : fintype walking_pair :=
{ elems := [walking_pair.left, walking_pair.right].to_finset,
  complete := λ x, by { cases x; simp } }

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

@[simp] lemma binary_fan.mk_π_app_left {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) :
  (binary_fan.mk π₁ π₂).π.app walking_pair.left = π₁ := rfl
@[simp] lemma binary_fan.mk_π_app_right {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) :
  (binary_fan.mk π₁ π₂).π.app walking_pair.right = π₂ := rfl
@[simp] lemma binary_cofan.mk_π_app_left {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
  (binary_cofan.mk ι₁ ι₂).ι.app walking_pair.left = ι₁ := rfl
@[simp] lemma binary_cofan.mk_π_app_right {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
  (binary_cofan.mk ι₁ ι₂).ι.app walking_pair.right = ι₂ := rfl

abbreviation prod (X Y : C) [has_limit (pair X Y)] := limit (pair X Y)
abbreviation coprod (X Y : C) [has_colimit (pair X Y)] := colimit (pair X Y)

abbreviation prod.fst (X Y : C) [has_limit (pair X Y)] : prod X Y ⟶ X := limit.π _ walking_pair.left
abbreviation prod.snd (X Y : C) [has_limit (pair X Y)] : prod X Y ⟶ Y := limit.π _ walking_pair.right

abbreviation prod.lift {W X Y : C} [has_limit (pair X Y)] (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ prod X Y :=
limit.lift _ (binary_fan.mk f g)

variables (C)

class has_binary_products :=
(has_limits_of_shape : has_limits_of_shape.{v} (discrete walking_pair) C)
class has_binary_coproducts :=
(has_colimits_of_shape : has_colimits_of_shape.{v} (discrete walking_pair) C)

attribute [instance] has_binary_products.has_limits_of_shape has_binary_coproducts.has_colimits_of_shape

variables {C} [has_binary_products.{v} C]

local attribute [tidy] tactic.case_bash

@[simp] def prod.braiding (P Q : C) : prod P Q ≅ prod Q P :=
{ hom := prod.lift (prod.snd P Q) (prod.fst P Q),
  inv := prod.lift (prod.snd Q P) (prod.fst Q P) }

def prod.symmetry (P Q : C) :
  (prod.braiding P Q).hom ≫ (prod.braiding Q P).hom = 𝟙 _ :=
by tidy

@[simp] def prod.associator
  (P Q R : C) : (prod (prod P Q) R) ≅ (prod P (prod Q R)) :=
{ hom :=
  prod.lift
    (prod.fst _ _ ≫ prod.fst _ _)
    (prod.lift (prod.fst _ _ ≫ prod.snd _ _) (prod.snd _ _)),
  inv :=
  prod.lift
    (prod.lift (prod.fst _ _) (prod.snd _ _ ≫ prod.fst _ _))
    (prod.snd _ _ ≫ prod.snd _ _) }

variables [has_terminal.{v} C]

@[simp] def prod.left_unitor
  (P : C) : (prod (terminal C) P) ≅ P :=
{ hom := prod.snd _ _,
  inv := prod.lift (terminal.from P) (𝟙 _) }

@[simp] def prod.right_unitor
  (P : C) : (prod P (terminal C)) ≅ P :=
{ hom := prod.fst _ _,
  inv := prod.lift (𝟙 _) (terminal.from P) }

end category_theory.limits
