-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.limits
import category_theory.limits.pullbacks

open category_theory

namespace category_theory.limits

local attribute [tidy] tactic.case_bash

universes u v w

inductive walking_pair : Type v
| zero | one

open walking_pair

inductive walking_pair_hom : walking_pair → walking_pair → Type v
| inl : walking_pair_hom zero one
| inr : walking_pair_hom zero one
| id : Π X : walking_pair.{v}, walking_pair_hom X X

open walking_pair_hom

instance walking_pair_category : small_category walking_pair :=
{ hom := walking_pair_hom,
  id := walking_pair_hom.id,
  comp := λ X Y Z f g, match X, Y, Z, f, g with
  | _, _ ,_, (id _), h := h
  | _, _, _, inl, (id one) := inl
  | _, _, _, inr, (id one) := inr
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
  | _, _, inl := f
  | _, _, inr := g
  end }.

@[simp] lemma pair_map_inl (f g : X ⟶ Y) : (pair f g).map inl = f := rfl
@[simp] lemma pair_map_inr (f g : X ⟶ Y) : (pair f g).map inr = g := rfl

@[simp] lemma pair_functor_obj {F : walking_pair.{v} ⥤ C} (j : walking_pair.{v}) :
  (pair (F.map inl) (F.map inr)).obj j = F.obj j :=
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

def fork.ι (t : fork f g) := t.π.app zero
def cofork.π (t : cofork f g) := t.ι.app one

def is_equalizer (t : fork f g) := is_limit t
def is_coequalizer (t : cofork f g) := is_colimit t

lemma is_equalizer.mono {t : fork f g} (h : is_equalizer t) : mono t.ι :=
⟨λ W (e₁ e₂ : W ⟶ t.X) H, begin
   unfold fork.ι at H,
   apply h.hom_ext,
   rintro (_|_),
   { exact H },
   { have : t.π.app one = t.π.app zero ≫ f, from (t.w inl).symm,
     rw [this, ←category.assoc, ←category.assoc, H] }
 end⟩

lemma is_coequalizer.epi {t : cofork f g} (h : is_coequalizer t) : epi t.π :=
⟨λ W (e₁ e₂ : t.X ⟶ W) H, begin
   unfold cofork.π at H,
   apply h.hom_ext,
   rintro (_|_),
   { have : t.ι.app zero = f ≫ t.ι.app one, from (t.w inl).symm,
     rw [this, category.assoc, category.assoc, H] },
   { exact H }
 end⟩

variables {t : fork f g}
variables {s : cofork f g}

instance is_equalizer_subsingleton : subsingleton (is_equalizer t) :=
by dsimp [is_equalizer]; apply_instance
instance is_coequalizer_subsingleton : subsingleton (is_coequalizer s) :=
by dsimp [is_coequalizer]; apply_instance

class has_equalizer {X Y : C} (f g : X ⟶ Y) :=
(fork : fork.{u v} f g)
(is_equalizer : is_equalizer fork . obviously)
class has_coequalizer {X Y : C} (f g : X ⟶ Y) :=
(cofork : cofork.{u v} f g)
(is_coequalizer : is_coequalizer cofork . obviously)

variable (C)

class has_equalizers :=
(fork : Π {X Y : C} (f g : X ⟶ Y), fork.{u v} f g)
(is_equalizer : Π {X Y : C} (f g : X ⟶ Y), is_equalizer (fork f g) . obviously)
class has_coequalizers :=
(cofork : Π {X Y : C} (f g : X ⟶ Y), cofork.{u v} f g)
(is_coequalizer : Π {X Y : C} (f g : X ⟶ Y), is_coequalizer (cofork f g) . obviously)

variable {C}

instance has_equalizer_of_has_equalizers [has_equalizers.{u v} C] {X Y : C} (f g : X ⟶ Y) :
  has_equalizer.{u v} f g :=
{ fork := has_equalizers.fork f g,
  is_equalizer := has_equalizers.is_equalizer C f g }
instance has_coequalizer_of_has_coequalizers [has_coequalizers.{u v} C] {X Y : C} (f g : X ⟶ Y) :
  has_coequalizer.{u v} f g :=
{ cofork := has_coequalizers.cofork f g,
  is_coequalizer := has_coequalizers.is_coequalizer C f g }

-- Special cases of this may be marked with [instance] as desired.
def has_equalizers_of_has_limits [limits.has_limits_of_shape.{u v} walking_pair C] :
  has_equalizers.{u v} C :=
{ fork := λ X Y f g, limit.cone (pair f g),
  is_equalizer := λ X Y f g, limit.universal_property (pair f g) }
def has_coequalizers_of_has_colimits [limits.has_colimits_of_shape.{u v} walking_pair C] :
  has_coequalizers.{u v} C :=
{ cofork := λ X Y f g, colimit.cocone (pair f g),
  is_coequalizer := λ X Y f g, colimit.universal_property (pair f g) }

@[simp] def cone.of_fork
  {F : walking_pair.{v} ⥤ C} (t : fork (F.map inl) (F.map inr)) : cone F :=
{ X := t.X,
  π :=
  { app := λ X, t.π.app X ≫ eq_to_hom (by tidy),
    naturality' := λ j j' g,
    begin
      cases j; cases j'; cases g; dsimp; simp,
      erw ← t.w inl, refl,
      erw ← t.w inr, refl,
    end } }.
@[simp] def cocone.of_cofork
  {F : walking_pair.{v} ⥤ C} (t : cofork (F.map inl) (F.map inr)) : cocone F :=
{ X := t.X,
  ι :=
  { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X,
    naturality' := λ j j' g,
    begin
      cases j; cases j'; cases g; dsimp; simp,
      erw ← t.w inl, refl,
      erw ← t.w inr, refl,
    end } }.

@[simp] def fork.of_cone
  {F : walking_pair.{v} ⥤ C} (t : cone F) : fork (F.map inl) (F.map inr) :=
{ X := t.X,
  π :=
  { app := λ X, t.π.app X ≫ eq_to_hom (by tidy) } }
@[simp] def cofork.of_cocone
  {F : walking_pair.{v} ⥤ C} (t : cocone F) : cofork (F.map inl) (F.map inr) :=
{ X := t.X,
  ι :=
  { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X } }

instance has_limits_of_shape_of_has_equalizers [has_equalizers.{u v} C] :
  limits.has_limits_of_shape.{u v} walking_pair.{v} C :=
{ cone := λ F, cone.of_fork (has_equalizers.fork (F.map inl) (F.map inr)),
  is_limit := λ F, let is_equalizer := has_equalizer.is_equalizer (F.map inl) (F.map inr) in
  { lift := λ s, is_equalizer.lift (fork.of_cone s),
    fac' := λ s j,
    begin
      convert is_equalizer.fac (fork.of_cone s) j; cases j,
      tidy,
    end,
    uniq' := λ s m w, is_equalizer.uniq (fork.of_cone s) m
      (λ j, begin convert w j; cases j, tidy end) } }

instance has_colimits_of_shape_of_has_coequalizers [has_coequalizers.{u v} C] :
  limits.has_colimits_of_shape.{u v} walking_pair.{v} C :=
{ cocone := λ F, cocone.of_cofork (has_coequalizers.cofork (F.map inl) (F.map inr)),
  is_colimit := λ F,
  let is_coequalizer := has_coequalizer.is_coequalizer (F.map inl) (F.map inr) in
  { desc := λ s, is_coequalizer.desc (cofork.of_cocone s),
    fac' := λ s j,
    begin
      convert is_coequalizer.fac (cofork.of_cocone s) j; cases j,
      tidy,
    end,
    uniq' := λ s m w, is_coequalizer.uniq (cofork.of_cocone s) m
      (λ j, begin convert w j; cases j, tidy end) } }

variable {C}

section
variables (f g)

def equalizer.fork [has_equalizer f g] : fork f g := has_equalizer.fork.{u v} f g
def coequalizer.cofork [has_coequalizer f g] : cofork f g := has_coequalizer.cofork.{u v} f g
def equalizer [has_equalizer f g] := (equalizer.fork f g).X
def coequalizer [has_coequalizer f g] := (coequalizer.cofork f g).X
def equalizer.ι [has_equalizer f g] : equalizer f g ⟶ X := (equalizer.fork f g).π.app zero
def coequalizer.π [has_coequalizer f g] : Y ⟶ coequalizer f g := (coequalizer.cofork f g).ι.app one
@[simp] lemma equalizer.w [has_equalizer f g] : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g :=
begin
  erw ((equalizer.fork f g).w inl),
  erw ((equalizer.fork f g).w inr)
end
@[simp] lemma coequalizer.w
  [has_coequalizer f g] : f ≫ coequalizer.π f g = g ≫ coequalizer.π f g :=
begin
  erw ((coequalizer.cofork f g).w inl),
  erw ((coequalizer.cofork f g).w inr)
end
def equalizer.universal_property [has_equalizer f g] : is_equalizer (equalizer.fork f g) :=
has_equalizer.is_equalizer f g
def coequalizer.universal_property
  [has_coequalizer f g] : is_coequalizer (coequalizer.cofork f g) :=
has_coequalizer.is_coequalizer f g

def equalizer.lift
  [has_equalizer f g] {P : C} (h : P ⟶ X) (w : h ≫ f = h ≫ g) : P ⟶ equalizer f g :=
(equalizer.universal_property f g).lift (fork.of_ι h w)
def coequalizer.desc
  [has_coequalizer f g] {P : C} (h : Y ⟶ P) (w : f ≫ h = g ≫ h) : coequalizer f g ⟶ P :=
(coequalizer.universal_property f g).desc (cofork.of_π h w)

@[simp] lemma equalizer.lift_ι [has_equalizer f g] {P : C} (h : P ⟶ X) (w : h ≫ f = h ≫ g) :
  equalizer.lift f g h w ≫ equalizer.ι f g = h :=
is_limit.fac _ _ _
@[simp] lemma coequalizer.π_desc [has_coequalizer f g] {P : C} (h : Y ⟶ P) (w : f ≫ h = g ≫ h) :
  coequalizer.π f g ≫ coequalizer.desc f g h w = h :=
is_colimit.fac _ _ _

instance [has_equalizer f g] : mono (equalizer.ι f g) :=
(has_equalizer.is_equalizer f g).mono
instance [has_coequalizer f g] : epi (coequalizer.π f g) :=
(has_coequalizer.is_coequalizer f g).epi

@[extensionality] lemma equalizer.hom_ext [has_equalizer f g] {P : C}
  {h k : P ⟶ equalizer f g}
  (w : h ≫ equalizer.ι f g = k ≫ equalizer.ι f g) : h = k := mono.right_cancellation h k w
@[extensionality] lemma coequalizer.hom_ext [has_coequalizer f g] {P : C}
  {h k : coequalizer f g ⟶ P}
  (w : coequalizer.π f g ≫ h = coequalizer.π f g ≫ k) : h = k := epi.left_cancellation h k w

end

end category_theory.limits
