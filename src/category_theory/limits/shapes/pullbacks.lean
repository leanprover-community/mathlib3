/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.fintype
import category_theory.limits.limits
import category_theory.sparse

/-!
# Pullbacks

We define a category `walking_cospan` (resp. `walking_span`), which is the index category
for the given data for a pullback (resp. pushout) diagram. Convenience methods `cospan f g`
and `span f g` construct functors from the walking (co)span, hitting the given morphisms.

We define `pullback f g` and `pushout f g` as limits and colimits of such functors.

Typeclasses `has_pullbacks` and `has_pushouts` assert the existence of (co)limits shaped as
walking (co)spans.
-/

open category_theory

namespace category_theory.limits

universes v u

local attribute [tidy] tactic.case_bash

/-- The type of objects for the diagram indexing a pullback. -/
@[derive decidable_eq] inductive walking_cospan : Type v
| left | right | one
/-- The type of objects for the diagram indexing a pushout. -/
@[derive decidable_eq] inductive walking_span : Type v
| zero | left | right

instance fintype_walking_cospan : fintype walking_cospan :=
{ elems := [walking_cospan.left, walking_cospan.right, walking_cospan.one].to_finset,
  complete := λ x, by { cases x; simp } }

instance fintype_walking_span : fintype walking_span :=
{ elems := [walking_span.zero, walking_span.left, walking_span.right].to_finset,
  complete := λ x, by { cases x; simp } }

namespace walking_cospan

/-- The arrows in a pullback diagram. -/
inductive hom : walking_cospan → walking_cospan → Type v
| inl : hom left one
| inr : hom right one
| id : Π X : walking_cospan.{v}, hom X X

open hom

def hom.comp : Π (X Y Z : walking_cospan) (f : hom X Y) (g : hom Y Z), hom X Z
| _ _ _ (id _) h := h
| _ _ _ inl    (id one) := inl
| _ _ _ inr    (id one) := inr
.

instance category_struct : category_struct walking_cospan :=
{ hom  := hom,
  id   := hom.id,
  comp := hom.comp, }

instance (X Y : walking_cospan) : subsingleton (X ⟶ Y) := by tidy

-- We make this a @[simp] lemma later; if we do it now there's a mysterious
-- failure in `cospan`, below.
lemma hom_id (X : walking_cospan.{v}) : hom.id X = 𝟙 X := rfl

/-- The walking_cospan is the index diagram for a pullback. -/
instance : small_category.{v} walking_cospan.{v} := sparse_category

end walking_cospan

namespace walking_span

/-- The arrows in a pushout diagram. -/
inductive hom : walking_span → walking_span → Type v
| fst : hom zero left
| snd : hom zero right
| id : Π X : walking_span.{v}, hom X X

open hom

def hom.comp : Π (X Y Z : walking_span) (f : hom X Y) (g : hom Y Z), hom X Z
  | _ _ _ (id _) h := h
  | _ _ _ fst    (id left) := fst
  | _ _ _ snd    (id right) := snd
.

instance category_struct : category_struct walking_span :=
{ hom  := hom,
  id   := hom.id,
  comp := hom.comp }

instance (X Y : walking_span) : subsingleton (X ⟶ Y) := by tidy

-- We make this a @[simp] lemma later; if we do it now there's a mysterious
-- failure in `span`, below.
lemma hom_id (X : walking_span.{v}) : hom.id X = 𝟙 X := rfl

/-- The walking_span is the index diagram for a pushout. -/
instance : small_category.{v} walking_span.{v} := sparse_category

end walking_span

open walking_span walking_cospan walking_span.hom walking_cospan.hom

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞

/-- `cospan f g` is the functor from the walking cospan hitting `f` and `g`. -/
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

/-- `span f g` is the functor from the walking span hitting `f` and `g`. -/
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
  (cospan f g).map walking_cospan.hom.inl = f := rfl
@[simp] lemma span_map_fst {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).map walking_span.hom.fst = f := rfl

@[simp] lemma cospan_map_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).map walking_cospan.hom.inr = g := rfl
@[simp] lemma span_map_snd {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).map walking_span.hom.snd = g := rfl

@[simp] lemma cospan_map_id {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : walking_cospan) :
  (cospan f g).map (walking_cospan.hom.id w) = 𝟙 _ := rfl
@[simp] lemma span_map_id {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (w : walking_span) :
  (span f g).map (walking_span.hom.id w) = 𝟙 _ := rfl


variables {X Y Z : C}

attribute [simp] walking_cospan.hom_id walking_span.hom_id

abbreviation pullback_cone (f : X ⟶ Z) (g : Y ⟶ Z) := cone (cospan f g)

namespace pullback_cone
variables {f : X ⟶ Z} {g : Y ⟶ Z}

def π₁ (t : pullback_cone f g) : t.X ⟶ X := t.π.app left
def π₂ (t : pullback_cone f g) : t.X ⟶ Y := t.π.app right

def mk {W : C} (π₁ : W ⟶ X) (π₂ : W ⟶ Y) (eq : π₁ ≫ f = π₂ ≫ g) : pullback_cone f g :=
{ X := W,
  π :=
  { app := λ j, walking_cospan.cases_on j π₁ π₂ (π₁ ≫ f),
    naturality' := λ j j' f, by cases f; obviously } }

lemma condition (t : pullback_cone f g) : (π₁ t) ≫ f = (π₂ t) ≫ g :=
begin
  erw [t.w inl, ← t.w inr], refl
end

end pullback_cone

abbreviation pushout_cocone (f : X ⟶ Y) (g : X ⟶ Z) := cocone (span f g)

namespace pushout_cocone

variables {f : X ⟶ Y} {g : X ⟶ Z}

def ι₁ (t : pushout_cocone f g) : Y ⟶ t.X := t.ι.app left
def ι₂ (t : pushout_cocone f g) : Z ⟶ t.X := t.ι.app right

def mk {W : C} (ι₁ : Y ⟶ W) (ι₂ : Z ⟶ W) (eq : f ≫ ι₁ = g ≫ ι₂) : pushout_cocone f g :=
{ X := W,
  ι :=
  { app := λ j, walking_span.cases_on j (f ≫ ι₁) ι₁ ι₂,
    naturality' := λ j j' f, by cases f; obviously } }

lemma condition (t : pushout_cocone f g) : f ≫ (ι₁ t) = g ≫ (ι₂ t) :=
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
  {F : walking_cospan.{v} ⥤ C} (t : pullback_cone (F.map inl) (F.map inr)) (j) :
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
  {F : walking_span.{v} ⥤ C} (t : pushout_cocone (F.map fst) (F.map snd)) (j) :
  (cocone.of_pushout_cocone t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl

def pullback_cone.of_cone
  {F : walking_cospan.{v} ⥤ C} (t : cone F) : pullback_cone (F.map inl) (F.map inr) :=
{ X := t.X,
  π := { app := λ j, t.π.app j ≫ eq_to_hom (by tidy) } }

@[simp] lemma pullback_cone.of_cone_π {F : walking_cospan.{v} ⥤ C} (t : cone F) (j) :
  (pullback_cone.of_cone t).π.app j = t.π.app j ≫ eq_to_hom (by tidy) := rfl

def pushout_cocone.of_cocone
  {F : walking_span.{v} ⥤ C} (t : cocone F) : pushout_cocone (F.map fst) (F.map snd) :=
{ X := t.X,
  ι := { app := λ j, eq_to_hom (by tidy) ≫ t.ι.app j } }

@[simp] lemma pushout_cocone.of_cocone_ι {F : walking_span.{v} ⥤ C} (t : cocone F) (j) :
  (pushout_cocone.of_cocone t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl


abbreviation pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_limit (cospan f g)] :=
limit (cospan f g)
abbreviation pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [has_colimit (span f g)] :=
colimit (span f g)

abbreviation pullback.π₁ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_limit (cospan f g)] : pullback f g ⟶ X :=
limit.π (cospan f g) walking_cospan.left
abbreviation pullback.π₂ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_limit (cospan f g)] : pullback f g ⟶ Y :=
limit.π (cospan f g) walking_cospan.right
abbreviation pushout.ι₁ {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [has_colimit (span f g)] : Y ⟶ pushout f g :=
colimit.ι (span f g) walking_span.left
abbreviation pushout.ι₂ {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [has_colimit (span f g)] : Z ⟶ pushout f g :=
colimit.ι (span f g) walking_span.right

abbreviation pullback.lift {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_limit (cospan f g)]
  (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g): W ⟶ pullback f g :=
limit.lift _ (pullback_cone.mk h k w)
abbreviation pushout.desc {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [has_colimit (span f g)]
  (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout f g ⟶ W :=
colimit.desc _ (pushout_cocone.mk h k w)

variables (C)

class has_pullbacks :=
(has_limits_of_shape : has_limits_of_shape.{v} walking_cospan C)
class has_pushouts :=
(has_colimits_of_shape : has_colimits_of_shape.{v} walking_span C)

attribute [instance] has_pullbacks.has_limits_of_shape has_pushouts.has_colimits_of_shape

end category_theory.limits
