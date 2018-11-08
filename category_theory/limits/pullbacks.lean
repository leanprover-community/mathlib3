-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.limits

open category_theory

namespace tactic
meta def case_bash : tactic unit :=
do l ← local_context,
   r ← successes (l.reverse.map (λ h, cases h >> skip)),
   when (r.empty) failed
end tactic

namespace category_theory.limits

universes u v w

local attribute [tidy] tactic.case_bash

inductive walking_cospan : Type v
| left | right | one
inductive walking_span : Type v
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

instance walking_cospan_category : small_category walking_cospan :=
{ hom := walking_cospan_hom,
  id := walking_cospan_hom.id,
  comp := λ X Y Z f g, match X, Y, Z, f, g with
  | _, _ ,_, (id _), h := h
  | _, _, _, inl, (id one) := inl
  | _, _, _, inr, (id one) := inr
  end }
instance walking_span_category : small_category walking_span :=
{ hom := walking_span_hom,
  id := walking_span_hom.id,
  comp := λ X Y Z f g, match X, Y, Z, f, g with
  | _, _ ,_, (id _), h := h
  | _, _, _, fst, (id left) := fst
  | _, _, _, snd, (id right) := snd
  end }

lemma walking_cospan_hom_id (X : walking_cospan.{v}) : walking_cospan_hom.id X = 𝟙 X := rfl
lemma walking_span_hom_id (X : walking_span.{v}) : walking_span_hom.id X = 𝟙 X := rfl

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : walking_cospan.{v} ⥤ C :=
{ obj := λ x, match x with
  | left := X
  | right := Y
  | one := Z
  end,
  map' := λ x y h, match x, y, h with
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
  map' := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, fst := f
  | _, _, snd := g
  end }

@[simp] lemma cospan_left {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  cospan f g walking_cospan.left = X := rfl
@[simp] lemma span_left {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  span f g walking_span.left = Y := rfl

@[simp] lemma cospan_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  cospan f g walking_cospan.right = Y := rfl
@[simp] lemma span_right {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  span f g walking_span.right = Z := rfl

@[simp] lemma cospan_one {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  cospan f g walking_cospan.one = Z := rfl
@[simp] lemma span_zero {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  span f g walking_span.zero = X := rfl

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

section pullback
def square (f : X ⟶ Z) (g : Y ⟶ Z) := cone (cospan f g)

variables {f : X ⟶ Z} {g : Y ⟶ Z}

def square.mk {W : C} (π₁ : W ⟶ X) (π₂ : W ⟶ Y)
  (eq : π₁ ≫ f = π₂ ≫ g) :
  square f g :=
{ X := W,
  π :=
  { app := λ j, walking_cospan.cases_on j π₁ π₂ (π₁ ≫ f),
    naturality' := λ j j' f, by cases f; obviously } }

def is_pullback (t : square f g) := is_limit t

variables {t : square f g}

instance is_pullback_subsingleton : subsingleton (is_pullback t) :=
by dsimp [is_pullback]; apply_instance

lemma is_pullback.hom_ext (p : is_pullback t) {W : C} {k h : W ⟶ t.X}
  (w_left : k ≫ t.π left = h ≫ t.π left)
  (w_right : k ≫ t.π right = h ≫ t.π right) : k = h :=
begin
 rw [p.hom_lift k, p.hom_lift h]; congr,
 ext j, cases j,
 exact w_left,
 exact w_right,
 have v := t.π.naturality walking_cospan_hom.inl,
 simp at v,
 erw category.id_comp at v,
 rw [v, ←category.assoc, w_left, category.assoc],
end

end pullback

section pushout
def cosquare (f : X ⟶ Y) (g : X ⟶ Z) := cocone (span f g)

variables {f : X ⟶ Y} {g : X ⟶ Z}

def cosquare.mk {W : C} (ι₁ : Y ⟶ W) (ι₂ : Z ⟶ W)
  (eq : f ≫ ι₁ = g ≫ ι₂) :
  cosquare f g :=
{ X := W,
  ι :=
  { app := λ j, walking_span.cases_on j (f ≫ ι₁) ι₁ ι₂,
    naturality' := λ j j' f, by cases f; obviously } }

def is_pushout (t : cosquare f g) := is_colimit t

variables {t : cosquare f g}

instance is_pushout_subsingleton : subsingleton (is_pushout t) :=
by dsimp [is_pushout]; apply_instance

lemma is_pushout.hom_ext (p : is_pushout t) {W : C} {k h : t.X ⟶ W}
  (w_left : t.ι left ≫ k = t.ι left ≫ h)
  (w_right : t.ι right ≫ k = t.ι right ≫ h) : k = h :=
begin
 rw [p.hom_desc k, p.hom_desc h]; congr,
 ext j, cases j,
 have v := t.ι.naturality walking_span_hom.fst,
 simp at v,
 erw category.comp_id at v,
 rw [←v, category.assoc, w_left, ←category.assoc],
 exact w_left,
 exact w_right,
end

end pushout

@[simp] def cone.of_square
  {F : walking_cospan.{v} ⥤ C} (t : square (F.map inl) (F.map inr)) : cone F :=
{ X := t.X,
  π :=
  { app := λ X, t.π.app X ≫ eq_to_hom (by tidy),
    naturality' := λ j j' g,
    begin
      cases j; cases j'; cases g; dsimp; simp,
      erw ← t.w inl, refl,
      erw ← t.w inr, refl,
    end } }.
@[simp] def cocone.of_cosquare
  {F : walking_span.{v} ⥤ C} (t : cosquare (F.map fst) (F.map snd)) : cocone F :=
{ X := t.X,
  ι :=
  { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X,
    naturality' := λ j j' g,
    begin
      cases j; cases j'; cases g; dsimp; simp,
      erw ← t.w fst, refl,
      erw ← t.w snd, refl,
    end } }.

@[simp] def square.of_cone
  {F : walking_cospan.{v} ⥤ C} (t : cone F) : square (F.map inl) (F.map inr) :=
{ X := t.X,
  π :=
  { app := λ X, t.π.app X ≫ eq_to_hom (by tidy) } }
@[simp] def cosquare.of_cocone
  {F : walking_span.{v} ⥤ C} (t : cocone F) : cosquare (F.map fst) (F.map snd) :=
{ X := t.X,
  ι :=
  { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X } }

variable (C)

class has_pullbacks :=
(square : Π {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), square.{u v} f g)
(is_pullback : Π {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), is_pullback (square f g) . obviously)
class has_pushouts :=
(cosquare : Π {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z), cosquare.{u v} f g)
(is_pushout : Π {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z), is_pushout (cosquare f g) . obviously)

variable {C}

-- Special cases of this may be marked with [instance] as desired.
def has_pullbacks_of_has_limits
  [limits.has_limits_of_shape.{u v} walking_cospan C] : has_pullbacks.{u v} C :=
{ square := λ X Y Z f g, limit.cone (cospan f g),
  is_pullback := λ X Y Z f g, limit.universal_property (cospan f g) }
def has_pushouts_of_has_colimits
  [limits.has_colimits_of_shape.{u v} walking_span C] : has_pushouts.{u v} C :=
{ cosquare := λ X Y Z f g, colimit.cocone (span f g),
  is_pushout := λ X Y Z f g, colimit.universal_property (span f g) }

section pullback
variable [has_pullbacks.{u v} C]
variables (f : X ⟶ Z) (g : Y ⟶ Z)

def pullback.square : square f g := has_pullbacks.square.{u v} f g
def pullback := (pullback.square f g).X
def pullback.π₁ : pullback f g ⟶ X := (pullback.square f g).π.app left
def pullback.π₂ : pullback f g ⟶ Y := (pullback.square f g).π.app right
@[simp] lemma pullback.w : pullback.π₁ f g ≫ f = pullback.π₂ f g ≫ g :=
begin
  erw ((pullback.square f g).w inl),
  erw ((pullback.square f g).w inr)
end
def pullback.universal_property : is_pullback (pullback.square f g) :=
has_pullbacks.is_pullback.{u v} C f g

instance has_limits_of_shape_of_has_pullbacks [has_pullbacks.{u v} C] :
  limits.has_limits_of_shape.{u v} walking_cospan.{v} C :=
{ cone := λ F, cone.of_square (pullback.square (F.map inl) (F.map inr)),
  is_limit := λ F, let is_pullback := pullback.universal_property (F.map inl) (F.map inr) in
  { lift := λ s, is_pullback.lift (square.of_cone s),
    fac' := λ s j,
    begin
      convert is_pullback.fac (square.of_cone s) j; cases j,
      tidy,
    end,
    uniq' := λ s m w, is_pullback.uniq (square.of_cone s) m
      (λ j, begin convert w j; cases j, tidy end) } }.

@[extensionality] lemma pullback.hom_ext [has_pullbacks.{u v} C] {W : C}
  {k h : W ⟶ pullback f g}
  (w_left : k ≫ pullback.π₁ f g = h ≫ pullback.π₁ f g)
  (w_right : k ≫ pullback.π₂ f g = h ≫ pullback.π₂ f g) : k = h :=
(pullback.universal_property f g).hom_ext w_left w_right

def pullback.lift [has_pullbacks.{u v} C] {W : C}
  (f' : W ⟶ X) (g' : W ⟶ Y) (eq : f' ≫ f = g' ≫ g) : W ⟶ pullback f g :=
(pullback.universal_property f g).lift (square.mk f' g' eq)

@[simp] lemma pullback.lift_π₁ [has_pullbacks.{u v} C] {W : C}
  (f' : W ⟶ X) (g' : W ⟶ Y) (eq : f' ≫ f = g' ≫ g) :
  pullback.lift f g f' g' eq ≫ pullback.π₁ f g = f' :=
(pullback.universal_property f g).fac (square.mk f' g' eq) _

@[simp] lemma pullback.lift_π₂ [has_pullbacks.{u v} C] {W : C}
  (f' : W ⟶ X) (g' : W ⟶ Y) (eq : f' ≫ f = g' ≫ g) :
  pullback.lift f g f' g' eq ≫ pullback.π₂ f g = g' :=
(pullback.universal_property f g).fac (square.mk f' g' eq) _

@[simp] lemma pullback.lift_id [has_pullbacks.{u v} C]
  (eq : pullback.π₁ f g ≫ f = pullback.π₂ f g ≫ g) :
  pullback.lift f g _ _ eq = 𝟙 _ :=
begin
  refine ((pullback.universal_property f g).uniq _ _ _).symm,
  rintros (_ | _ | _),
  { dsimp [square.mk], simp, refl },
  { dsimp [square.mk], simp, refl },
  { dsimp [square.mk], simp,
    have := (pullback.square f g).π.naturality walking_cospan_hom.inr,
    dsimp at this,
    simpa }
end

end pullback

section pushout
variable [has_pushouts.{u v} C]
variables (f : X ⟶ Y) (g : X ⟶ Z)

def pushout.cosquare : cosquare f g := has_pushouts.cosquare.{u v} f g
def pushout := (pushout.cosquare f g).X
def pushout.ι₁ : Y ⟶ pushout f g := (pushout.cosquare f g).ι.app left
def pushout.ι₂ : Z ⟶ pushout f g := (pushout.cosquare f g).ι.app right
@[simp] lemma pushout.w : f ≫ pushout.ι₁ f g = g ≫ pushout.ι₂ f g :=
begin
  erw ((pushout.cosquare f g).w fst),
  erw ((pushout.cosquare f g).w snd)
end
def pushout.universal_property : is_pushout (pushout.cosquare f g) :=
has_pushouts.is_pushout.{u v} C f g

instance has_colimits_of_shape_of_has_pushouts [has_pushouts.{u v} C] :
  limits.has_colimits_of_shape.{u v} walking_span.{v} C :=
{ cocone := λ F, cocone.of_cosquare (pushout.cosquare (F.map fst) (F.map snd)),
  is_colimit := λ F, let is_pushout := pushout.universal_property (F.map fst) (F.map snd) in
  { desc := λ s, is_pushout.desc (cosquare.of_cocone s),
    fac' := λ s j,
    begin
      convert is_pushout.fac (cosquare.of_cocone s) j; cases j,
      tidy,
    end,
    uniq' := λ s m w, is_pushout.uniq (cosquare.of_cocone s) m
      (λ j, begin convert w j; cases j, tidy end) } }.

@[extensionality] lemma pushout.hom_ext [has_pushouts.{u v} C] {W : C}
  {k h : pushout f g ⟶ W}
  (w_left : pushout.ι₁ f g ≫ k = pushout.ι₁ f g ≫ h)
  (w_right : pushout.ι₂ f g ≫ k = pushout.ι₂ f g ≫ h) : k = h :=
(pushout.universal_property f g).hom_ext w_left w_right

def pushout.desc [has_pushouts.{u v} C] {W : C}
  (f' : Y ⟶ W) (g' : Z ⟶ W) (eq : f ≫ f' = g ≫ g') : pushout f g ⟶ W :=
(pushout.universal_property f g).desc (cosquare.mk f' g' eq)

@[simp] lemma pushout.lift_π₁ [has_pushouts.{u v} C] {W : C}
  (f' : Y ⟶ W) (g' : Z ⟶ W) (eq : f ≫ f' = g ≫ g') :
  pushout.ι₁ f g ≫ pushout.desc f g f' g' eq = f' :=
(pushout.universal_property f g).fac (cosquare.mk f' g' eq) _

@[simp] lemma pushout.lift_π₂ [has_pushouts.{u v} C] {W : C}
  (f' : Y ⟶ W) (g' : Z ⟶ W) (eq : f ≫ f' = g ≫ g') :
  pushout.ι₂ f g ≫ pushout.desc f g f' g' eq = g' :=
(pushout.universal_property f g).fac (cosquare.mk f' g' eq) _

@[simp] lemma pushout.lift_id [has_pushouts.{u v} C]
  (eq : f ≫ pushout.ι₁ f g = g ≫ pushout.ι₂ f g) :
  pushout.desc f g _ _ eq = 𝟙 _ :=
begin
  refine ((pushout.universal_property f g).uniq _ _ _).symm,
  rintros (_ | _ | _),
  { dsimp [cosquare.mk], simp,
    have := (pushout.cosquare f g).ι.naturality walking_span_hom.snd,
    dsimp at this,
    erw ← this,
    simpa },
  { dsimp [cosquare.mk], erw category.comp_id, refl },
  { dsimp [cosquare.mk], erw category.comp_id, refl },
end

end pushout

end category_theory.limits
