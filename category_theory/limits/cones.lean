-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.natural_isomorphism
import category_theory.whiskering
import category_theory.discrete_category
import category_theory.const

universes u u' v

open category_theory

variables (J : Type v) [small_category J]
variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

variables {J C}
open category_theory
open category_theory.functor

namespace category_theory.limits

/--
A `c : cone F` is:
* an object `c.X` and
* a natural transformation `c.π : c.X ⟹ F` from the constant `c.X` functor to `F`.
-/
structure cone (F : J ⥤ C) :=
(X : C)
(π : (const J).obj X ⟹ F)

@[simp] lemma cone.w {F : J ⥤ C} (c : cone F) {j j' : J} (f : j ⟶ j') :
  c.π.app j ≫ F.map f = c.π.app j' :=
begin
  have h := (c.π).naturality f,
  simp at h,
  erw category.id_comp at h,
  exact eq.symm h
end

/--
A `c : cocone F` is
* an object `c.X` and
* a natural transformation `c.ι : F ⟹ c.X` from `F` to the constant `c.X` functor.
-/
structure cocone (F : J ⥤ C) :=
(X : C)
(ι : F ⟹ (const J).obj X)

@[simp] lemma cocone.w {F : J ⥤ C} (c : cocone F) {j j' : J} (f : j ⟶ j') :
  F.map f ≫ c.ι.app j' = c.ι.app j :=
begin
  have h := (c.ι).naturality f,
  simp at h,
  erw category.comp_id at h,
  exact h
end

variable {F : J ⥤ C}

namespace functor
-- These are not particularly important definitions; they're mostly here
-- as reminders of the relationship between `F.cones` and `cone F`.

def cones_of_cone (c : cone F) : F.cones.obj c.X := c.π
def cone_of_cones {X : C} (π : F.cones.obj X) : cone F :=
{ X := X,
  π := π }
end functor

namespace cone
@[simp] def extensions (c : cone F) : yoneda.obj c.X ⟶ F.cones :=
{ app := λ X f, ((const J).map f) ⊟ c.π }

@[simp] def extend (c : cone F) {X : C} (f : X ⟶ c.X) : cone F :=
{ X := X,
  π := c.extensions.app X f }

def postcompose {G : J ⥤ C} (c : cone F) (α : F ⟹ G) : cone G :=
{ X := c.X,
  π := c.π ⊟ α }

def whisker (c : cone F) {K : Type v} [small_category K] (E : K ⥤ J) : cone (E ⋙ F) :=
{ X := c.X,
  π := whisker_left E c.π }

@[simp] lemma whisker_π_app (c : cone F) {K : Type v} [small_category K] (E : K ⥤ J) (k : K) :
  (c.whisker E).π.app k = (c.π).app (E.obj k) := rfl
end cone

namespace cocone
def extend (c : cocone F) {X : C} (f : c.X ⟶ X) : cocone F :=
{ X := X,
  ι := c.ι ⊟ (const J).map f }

def precompose {G : J ⥤ C} (c : cocone F) (α : G ⟹ F) : cocone G :=
{ X := c.X,
  ι := α ⊟ c.ι }

def whisker (c : cocone F) {K : Type v} [small_category K] (E : K ⥤ J) : cocone (E ⋙ F) :=
{ X := c.X,
  ι := whisker_left E c.ι }

@[simp] lemma whisker_ι_app (c : cocone F) {K : Type v} [small_category K] (E : K ⥤ J) (k : K) :
  (c.whisker E).ι.app k = (c.ι).app (E.obj k) := rfl
end cocone

structure cone_morphism (A B : cone F) :=
(hom : A.X ⟶ B.X)
(w'  : Π j : J, hom ≫ (B.π.app j) = (A.π.app j) . obviously)

restate_axiom cone_morphism.w'
attribute [simp] cone_morphism.w

namespace cone_morphism

@[extensionality] lemma ext {A B : cone F} {f g : cone_morphism A B} (w : f.hom = g.hom) : f = g :=
begin
  induction f,
  induction g,
  -- `obviously'` says:
  dsimp at w,
  induction w,
  refl,
end
end cone_morphism

instance cones (F : J ⥤ C) : category.{(max u v) v} (cone F) :=
{ hom  := λ A B, cone_morphism A B,
  comp := λ X Y Z f g,
  { hom := f.hom ≫ g.hom,
    w' := begin intros j, rw category.assoc, rw cone_morphism.w g, rw cone_morphism.w f j end },
  id   := λ B, { hom := 𝟙 B.X } }

namespace cones
@[simp] lemma id.hom   {F : J ⥤ C} (c : cone F) : (𝟙 c : cone_morphism c c).hom = 𝟙 (c.X) := rfl
@[simp] lemma comp.hom {F : J ⥤ C} {c d e : cone F} (f : c ⟶ d) (g : d ⟶ e) :
  ((f ≫ g) : cone_morphism c e).hom = (f : cone_morphism c d).hom ≫ (g : cone_morphism d e).hom :=
rfl

@[extensionality] def ext
  {F : J ⥤ C} (c c' : cone F) (φ : c.X ≅ c'.X) (w : ∀ j, c.π.app j = φ.hom ≫ c'.π.app j) :
  c ≅ c' :=
{ hom :=
  { hom := φ.hom },
  inv :=
  { hom := φ.symm.hom,
    w' := λ j,
    begin
      have h := congr_arg (λ p, φ.inv ≫ p) (w j),
      dsimp at h,
      erw h,
      rw ←category.assoc,
      simp,
    end } }

section
variables {D : Type u'} [𝒟 : category.{u' v} D]
include 𝒟

@[simp] def functoriality (F : J ⥤ C) (G : C ⥤ D) : (cone F) ⥤ (cone (F ⋙ G)) :=
{ obj := λ A,
  { X := G.obj A.X,
    π := (functor.const_compose _ _ _).hom ⊟ whisker_right A.π G },
  map := λ X Y f,
  { hom := G.map f.hom,
    w' := begin intros, dsimp, simp, rw [←functor.map_comp, f.w], end } }
end
end cones

structure cocone_morphism (A B : cocone F) :=
(hom : A.X ⟶ B.X)
(w'  : Π j : J, (A.ι.app j) ≫ hom = (B.ι.app j) . obviously)

restate_axiom cocone_morphism.w'
attribute [simp] cocone_morphism.w

namespace cocone_morphism

@[extensionality] lemma ext
  {A B : cocone F} {f g : cocone_morphism A B} (w : f.hom = g.hom) : f = g :=
begin
  induction f,
  induction g,
  -- `obviously'` says:
  dsimp at w,
  induction w,
  refl,
end
end cocone_morphism

instance cocones (F : J ⥤ C) : category.{(max u v) v} (cocone F) :=
{ hom  := λ A B, cocone_morphism A B,
  comp := λ _ _ _ f g,
  { hom := f.hom ≫ g.hom,
    w' :=
    begin
      intros j, rw [←category.assoc, ←cocone_morphism.w g, ←cocone_morphism.w f j]
    end },
  id   := λ B, { hom := 𝟙 B.X } }

namespace cocones
@[simp] lemma id.hom   {F : J ⥤ C} (c : cocone F) :
  (𝟙 c : cocone_morphism c c).hom = 𝟙 (c.X) := rfl
@[simp] lemma comp.hom {F : J ⥤ C} {c d e : cocone F} (f : c ⟶ d) (g : d ⟶ e) : ((f ≫ g) :
  cocone_morphism c e).hom = (f : cocone_morphism c d).hom ≫ (g : cocone_morphism d e).hom := rfl

@[extensionality] def ext
  {F : J ⥤ C} (c c' : cocone F) (φ : c.X ≅ c'.X) (w : ∀ j, c.ι.app j ≫ φ.hom = c'.ι.app j):
  c ≅ c' :=
{ hom :=
  { hom := φ.hom },
  inv :=
  { hom := φ.symm.hom,
    w' := λ j,
    begin
      have h := congr_arg (λ p, p ≫ φ.inv) (w j),
      dsimp at h,
      erw ←h,
      rw category.assoc,
      simp,
    end } }

section
variables {D : Type u'} [𝒟 : category.{u' v} D]
include 𝒟

@[simp] def functoriality (F : J ⥤ C) (G : C ⥤ D) : (cocone F) ⥤ (cocone (F ⋙ G)) :=
{ obj := λ A,
  { X := G.obj A.X,
    ι :=
    { app := λ j, G.map (A.ι.app j), naturality' := by intros; erw ←G.map_comp; tidy } },
  map := λ _ _ f,
  { hom := G.map f.hom,
    w'  :=
    begin
      intros, dsimp,
      erw [←functor.map_comp, cocone_morphism.w],
    end } }
end

def vertex {F : J ⥤ C} : cocone F ⥤ C :=
{ obj := λ A, A.X, map := λ A B f, f.hom }
end cocones

end category_theory.limits

namespace category_theory.functor

variables {D : Type u'} [category.{u' v} D]
variables {F : J ⥤ C} {G : J ⥤ C}

open category_theory.limits

def map_cone   (H : C ⥤ D) (c : cone F)   : cone (F ⋙ H)   := (cones.functoriality F H).obj c
def map_cocone (H : C ⥤ D) (c : cocone F) : cocone (F ⋙ H) := (cocones.functoriality F H).obj c
def map_cone_morphism   (H : C ⥤ D) {c c' : cone F}   (f : cone_morphism c c')   :
  cone_morphism   (H.map_cone c)   (H.map_cone c')   := (cones.functoriality F H).map f
def map_cocone_morphism (H : C ⥤ D) {c c' : cocone F} (f : cocone_morphism c c') :
  cocone_morphism (H.map_cocone c) (H.map_cocone c') := (cocones.functoriality F H).map f

@[simp] lemma map_cone_π (H : C ⥤ D) (c : cone F) (j : J) :
  (map_cone H c).π.app j = 𝟙 _ ≫ H.map (c.π.app j) := rfl
@[simp] lemma map_cocone_ι (H : C ⥤ D) (c : cocone F) (j : J) :
  (map_cocone H c).ι.app j = H.map (c.ι.app j) := rfl

end category_theory.functor
