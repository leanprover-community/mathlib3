-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.eq_to_hom
import category_theory.limits.cones
import category_theory.sparse

open category_theory

namespace tactic
meta def case_bash : tactic unit :=
do l ← local_context,
   r ← successes (l.reverse.map (λ h, cases h >> skip)),
   when (r.empty) failed
end tactic

namespace category_theory.limits

universes v u

local attribute [tidy] tactic.case_bash

@[derive decidable_eq] inductive walking_cospan : Type v
| left | right | one
@[derive decidable_eq] inductive walking_span : Type v
| zero | left | right

open walking_cospan
open walking_span

inductive walking_cospan_hom : walking_cospan → walking_cospan → Type v
| inl : walking_cospan_hom left one
| inr : walking_cospan_hom right one
| id : Π X : walking_cospan.{v}, walking_cospan_hom X X
inductive walking_span_hom : walking_span → walking_span → Type v
| fst : walking_span_hom zero left
| snd : walking_span_hom zero right
| id : Π X : walking_span.{v}, walking_span_hom X X

open walking_cospan_hom
open walking_span_hom

def walking_cospan_comp :
  Π (X Y Z : walking_cospan) (f : walking_cospan_hom X Y) (g : walking_cospan_hom Y Z),
    walking_cospan_hom X Z
| _ _ _ (id _) h := h
| _ _ _ inl    (id one) := inl
| _ _ _ inr    (id one) := inr
.

def walking_span_comp :
  Π (X Y Z : walking_span) (f : walking_span_hom X Y) (g : walking_span_hom Y Z),
    walking_span_hom X Z
  | _ _ _ (id _) h := h
  | _ _ _ fst    (id left) := fst
  | _ _ _ snd    (id right) := snd
.

instance walking_cospan_category_struct : category_struct walking_cospan :=
{ hom  := walking_cospan_hom,
  id   := walking_cospan_hom.id,
  comp := walking_cospan_comp, }

instance walking_cospan_sparse (X Y : walking_cospan) : subsingleton (X ⟶ Y) :=
begin
  cases X; cases Y; { split, intros, cases a; cases b; refl },
end

instance walking_span_category_struct : category_struct walking_span :=
{ hom  := walking_span_hom,
  id   := walking_span_hom.id,
  comp := walking_span_comp }

instance walking_span_sparse (X Y : walking_span) : subsingleton (X ⟶ Y) :=
begin
  cases X; cases Y; { split, intros, cases a; cases b; refl },
end

lemma walking_cospan_hom_id (X : walking_cospan.{v}) : walking_cospan_hom.id X = 𝟙 X := rfl
lemma walking_span_hom_id (X : walking_span.{v}) : walking_span_hom.id X = 𝟙 X := rfl

instance walking_cospan_category : small_category.{v+1} walking_cospan.{v} := sparse_category
instance walking_span_category : small_category.{v+1} walking_span.{v} := sparse_category

variables {C : Sort u} [𝒞 : category.{v+1} C]
include 𝒞

def cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : walking_cospan.{v} ⥤ C :=
{ obj := λ x, match x with
  | left := X
  | right := Y
  | one := Z
  end,
  map := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, inl := f
  | _, _, inr := g
  end }
def span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : walking_span.{v} ⥤ C :=
{ obj := λ x, match x with
  | zero := X
  | left := Y
  | right := Z
  end,
  map := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, fst := f
  | _, _, snd := g
  end }

@[simp] lemma cospan_left {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).obj walking_cospan.left = X := rfl
@[simp] lemma span_left {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).obj walking_span.left = Y := rfl

@[simp] lemma cospan_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).obj walking_cospan.right = Y := rfl
@[simp] lemma span_right {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).obj walking_span.right = Z := rfl

@[simp] lemma cospan_one {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).obj walking_cospan.one = Z := rfl
@[simp] lemma span_zero {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).obj walking_span.zero = X := rfl

@[simp] lemma cospan_map_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).map walking_cospan_hom.inl = f := rfl
@[simp] lemma span_map_fst {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).map walking_span_hom.fst = f := rfl

@[simp] lemma cospan_map_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).map walking_cospan_hom.inr = g := rfl
@[simp] lemma span_map_snd {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).map walking_span_hom.snd = g := rfl

@[simp] lemma cospan_map_id {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : walking_cospan) :
  (cospan f g).map (walking_cospan_hom.id w) = 𝟙 _ := rfl
@[simp] lemma span_map_id {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (w : walking_span) :
  (span f g).map (walking_span_hom.id w) = 𝟙 _ := rfl


variables {X Y Z : C}

attribute [simp] walking_cospan_hom_id walking_span_hom_id

def pullback_cone (f : X ⟶ Z) (g : Y ⟶ Z) := cone (cospan f g)

namespace pullback_cone
variables {f : X ⟶ Z} {g : Y ⟶ Z}

def π₁ (t : pullback_cone f g) : t.X ⟶ X := t.π.app left
def π₂ (t : pullback_cone f g) : t.X ⟶ Y := t.π.app right

def mk {W : C} (π₁ : W ⟶ X) (π₂ : W ⟶ Y)
  (eq : π₁ ≫ f = π₂ ≫ g) :
  pullback_cone f g :=
{ X := W,
  π :=
  { app := λ j, walking_cospan.cases_on j π₁ π₂ (π₁ ≫ f),
    naturality' := λ j j' f, by cases f; obviously } }

def condition (t : pullback_cone f g) : (π₁ t) ≫ f = (π₂ t) ≫ g :=
begin
  erw [t.w inl, ← t.w inr], refl
end

end pullback_cone

def pushout_cocone (f : X ⟶ Y) (g : X ⟶ Z) := cocone (span f g)

namespace pushout_cocone

variables {f : X ⟶ Y} {g : X ⟶ Z}

def ι₁ (t : pushout_cocone f g) : Y ⟶ t.X := t.ι.app left
def ι₂ (t : pushout_cocone f g) : Z ⟶ t.X := t.ι.app right

def mk {W : C} (ι₁ : Y ⟶ W) (ι₂ : Z ⟶ W)
  (eq : f ≫ ι₁ = g ≫ ι₂) :
  pushout_cocone f g :=
{ X := W,
  ι :=
  { app := λ j, walking_span.cases_on j (f ≫ ι₁) ι₁ ι₂,
    naturality' := λ j j' f, by cases f; obviously } }

def condition (t : pushout_cocone f g) : f ≫ (ι₁ t) = g ≫ (ι₂ t) :=
begin
  erw [t.w fst, ← t.w snd], refl
end

end pushout_cocone

def cone.of_pullback_cone
  {F : walking_cospan.{v} ⥤ C} (t : pullback_cone (F.map inl) (F.map inr)) : cone F :=
{ X := t.X,
  π :=
  { app := λ X, t.π.app X ≫ eq_to_hom (by tidy),
    naturality' := λ j j' g,
    begin
      cases j; cases j'; cases g; dsimp; simp,
      erw ← t.w inl, refl,
      erw ← t.w inr, refl,
    end } }.

@[simp] lemma cone.of_pullback_cone_π
  {F : walking_cospan.{v} ⥤ C} (t : pullback_cone (F.map inl) (F.map inr)) (j):
  (cone.of_pullback_cone t).π.app j = t.π.app j ≫ eq_to_hom (by tidy) := rfl

def cocone.of_pushout_cocone
  {F : walking_span.{v} ⥤ C} (t : pushout_cocone (F.map fst) (F.map snd)) : cocone F :=
{ X := t.X,
  ι :=
  { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X,
    naturality' := λ j j' g,
    begin
      cases j; cases j'; cases g; dsimp; simp,
      erw ← t.w fst, refl,
      erw ← t.w snd, refl,
    end } }.

@[simp] lemma cocone.of_pushout_cocone_ι
  {F : walking_span.{v} ⥤ C} (t : pushout_cocone (F.map fst) (F.map snd)) (j):
  (cocone.of_pushout_cocone t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl

def pullback_cone.of_cone
  {F : walking_cospan.{v} ⥤ C} (t : cone F) : pullback_cone (F.map inl) (F.map inr) :=
{ X := t.X,
  π :=
  { app := λ j, t.π.app j ≫ eq_to_hom (by tidy) } }

@[simp] lemma pullback_cone.of_cone_π {F : walking_cospan.{v} ⥤ C} (t : cone F) (j) :
  (pullback_cone.of_cone t).π.app j = t.π.app j ≫ eq_to_hom (by tidy) := rfl

def pushout_cocone.of_cocone
  {F : walking_span.{v} ⥤ C} (t : cocone F) : pushout_cocone (F.map fst) (F.map snd) :=
{ X := t.X,
  ι :=
  { app := λ j, eq_to_hom (by tidy) ≫ t.ι.app j } }

@[simp] lemma pushout_cocone.of_cocone_ι {F : walking_span.{v} ⥤ C} (t : cocone F) (j) :
  (pushout_cocone.of_cocone t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl

end category_theory.limits
