-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.shapes.pullbacks

open category_theory

namespace category_theory.limits

local attribute [tidy] tactic.case_bash

universes u v

@[derive decidable_eq] inductive walking_pair : Type v
| zero | one

open walking_pair

inductive walking_pair_hom : walking_pair → walking_pair → Type v
| left : walking_pair_hom zero one
| right : walking_pair_hom zero one
| id : Π X : walking_pair.{v}, walking_pair_hom X X

open walking_pair_hom

instance walking_pair_category : small_category walking_pair :=
{ hom := walking_pair_hom,
  id := walking_pair_hom.id,
  comp := λ X Y Z f g, match X, Y, Z, f, g with
  | _, _ ,_, (id _), h := h
  | _, _, _, left, (id one) := left
  | _, _, _, right, (id one) := right
  end }

lemma walking_pair_hom_id (X : walking_pair.{v}) : walking_pair_hom.id X = 𝟙 X := rfl

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞
variables {X Y : C}

def pair (f g : X ⟶ Y) : walking_pair.{v} ⥤ C :=
{ obj := λ x, match x with
  | zero := X
  | one := Y
  end,
  map := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, left := f
  | _, _, right := g
  end }.

@[simp] lemma pair_map_left (f g : X ⟶ Y) : (pair f g).map left = f := rfl
@[simp] lemma pair_map_right (f g : X ⟶ Y) : (pair f g).map right = g := rfl

@[simp] lemma pair_functor_obj {F : walking_pair.{v} ⥤ C} (j : walking_pair.{v}) :
  (pair (F.map left) (F.map right)).obj j = F.obj j :=
begin
  cases j; refl
end

def fork (f g : X ⟶ Y) := cone (pair f g)
def cofork (f g : X ⟶ Y) := cocone (pair f g)

variables {f g : X ⟶ Y}

attribute [simp] walking_pair_hom_id

def fork.of_ι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : fork f g :=
{ X := P,
  π :=
  { app := λ X, begin cases X, exact ι, exact ι ≫ f, end,
    naturality' := λ X Y f,
    begin
      cases X; cases Y; cases f; dsimp; simp,
      exact w
    end }}
def cofork.of_π {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : cofork f g :=
{ X := P,
  ι :=
  { app := λ X, begin cases X, exact f ≫ π, exact π, end,
    naturality' := λ X Y f,
    begin
      cases X; cases Y; cases f; dsimp; simp,
      exact eq.symm w
    end }}

@[simp] lemma fork.of_ι_app_zero {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) :
  (fork.of_ι ι w).π.app zero = ι := rfl
@[simp] lemma fork.of_ι_app_one {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) :
  (fork.of_ι ι w).π.app one = ι ≫ f := rfl

def fork.ι (t : fork f g) := t.π.app zero
def cofork.π (t : cofork f g) := t.ι.app one
def fork.condition (t : fork f g) : (fork.ι t) ≫ f = (fork.ι t) ≫ g :=
begin
  erw [t.w left, ← t.w right], refl
end
def cofork.condition (t : cofork f g) : f ≫ (cofork.π t) = g ≫ (cofork.π t) :=
begin
  erw [t.w left, ← t.w right], refl
end

def cone.of_fork
  {F : walking_pair.{v} ⥤ C} (t : fork (F.map left) (F.map right)) : cone F :=
{ X := t.X,
  π :=
  { app := λ X, t.π.app X ≫ eq_to_hom (by tidy),
    naturality' := λ j j' g,
    begin
      cases j; cases j'; cases g; dsimp; simp,
      erw ← t.w left, refl,
      erw ← t.w right, refl,
    end } }.
def cocone.of_cofork
  {F : walking_pair.{v} ⥤ C} (t : cofork (F.map left) (F.map right)) : cocone F :=
{ X := t.X,
  ι :=
  { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X,
    naturality' := λ j j' g,
    begin
      cases j; cases j'; cases g; dsimp; simp,
      erw ← t.w left, refl,
      erw ← t.w right, refl,
    end } }.

@[simp] lemma cone.of_fork_π
  {F : walking_pair.{v} ⥤ C} (t : fork (F.map left) (F.map right)) (j):
  (cone.of_fork t).π.app j = t.π.app j ≫ eq_to_hom (by tidy) := rfl

@[simp] lemma cocone.of_cofork_ι
  {F : walking_pair.{v} ⥤ C} (t : cofork (F.map left) (F.map right)) (j):
  (cocone.of_cofork t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl

def fork.of_cone
  {F : walking_pair.{v} ⥤ C} (t : cone F) : fork (F.map left) (F.map right) :=
{ X := t.X,
  π := { app := λ X, t.π.app X ≫ eq_to_hom (by tidy) } }
def cofork.of_cocone
  {F : walking_pair.{v} ⥤ C} (t : cocone F) : cofork (F.map left) (F.map right) :=
{ X := t.X,
  ι := { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X } }

@[simp] lemma fork.of_cone_π {F : walking_pair.{v} ⥤ C} (t : cone F) (j) :
  (fork.of_cone t).π.app j = t.π.app j ≫ eq_to_hom (by tidy) := rfl
@[simp] lemma cofork.of_cocone_ι {F : walking_pair.{v} ⥤ C} (t : cocone F) (j) :
  (cofork.of_cocone t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl

end category_theory.limits
