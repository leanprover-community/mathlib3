/-
Copyright (c) 2019 Scott Morrison All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

The core of a category C is the groupoid whose morphisms are all the
isomorphisms of C.
-/

import category_theory.groupoid
import category_theory.whiskering

namespace category_theory

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

def core (C : Type u₁) := C

variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

instance core_category : groupoid.{(max v₁ 1)} (core C) :=
{ hom  := λ X Y : C, X ≅ Y,
  inv  := λ X Y f, iso.symm f,
  id   := λ X, iso.refl X,
  comp := λ X Y Z f g, iso.trans f g }

namespace core
@[simp] lemma id_hom (X : core C) : iso.hom (𝟙 X) = 𝟙 X := rfl
@[simp] lemma comp_hom {X Y Z : core C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom :=
rfl

def inclusion : core C ⥤ C :=
{ obj := id,
  map := λ X Y f, f.hom }

variables {G : Type u₂} [𝒢 : groupoid.{v₂} G]
include 𝒢

/-- A functor from a groupoid to a category C factors through the core of C. -/
-- Note that this function is not functorial
-- (consider the two functors from [0] to [1], and the natural transformation between them).
def functor_to_core (F : G ⥤ C) : G ⥤ core C :=
{ obj := λ X, F.obj X,
  map := λ X Y f, ⟨F.map f, F.map (inv f)⟩ }

def forget_functor_to_core : (G ⥤ core C) ⥤ (G ⥤ C) := (whiskering_right _ _ _).obj inclusion
end core

end category_theory
