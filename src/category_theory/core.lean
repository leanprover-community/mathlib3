/-
Copyright (c) 2019 Scott Morrison All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.groupoid
import control.equiv_functor
import category_theory.types

namespace category_theory

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

/-- The core of a category C is the groupoid whose morphisms are all the
isomorphisms of C. -/
def core (C : Type u₁) := C

namespace core
variables {C : Type u₁}

def lift (X : C) : core C := X
def desc (X : core C) : C := X

@[simp] lemma lift_desc {X : core C} : lift (desc X) = X := rfl
@[simp] lemma desc_lift {X : C} : desc (lift X) = X := rfl

attribute [irreducible] core
end core

open core

variables {C : Type u₁} [category.{v₁} C]

instance core_category : groupoid.{v₁} (core C) :=
{ hom  := λ X Y, desc X ≅ desc Y,
  inv  := λ X Y f, iso.symm f,
  id   := λ X, iso.refl (desc X),
  comp := λ X Y Z f g, iso.trans f g }

namespace core
@[simp] lemma id_hom (X : core C) : iso.hom (𝟙 X) = 𝟙 (desc X) := rfl
@[simp] lemma comp_hom {X Y Z : core C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom :=
rfl

def lift_iso_to_iso {X Y : C} (f : X ≅ Y) : lift X ≅ lift Y :=
{ hom := f,
  inv := f.symm, }

def desc_hom {X Y : core C} (f : X ⟶ Y) : desc X ≅ desc Y := f

@[simp] lemma desc_hom_id {X : core C} : desc_hom (𝟙 X) = iso.refl (desc X) := rfl
@[simp] lemma desc_hom_comp {X Y Z : core C} {f : X ⟶ Y} {g : Y ⟶ Z} :
  desc_hom (f ≫ g) = desc_hom f ≪≫ desc_hom g := rfl

/-- The core of a category is naturally included in the category. -/
def inclusion : core C ⥤ C :=
{ obj := desc,
  map := λ X Y f, f.hom }

variables {G : Type u₂} [groupoid.{v₂} G]

/-- A functor from a groupoid to a category C factors through the core of C. -/
-- Note that this function is not functorial
-- (consider the two functors from [0] to [1], and the natural transformation between them).
def functor_to_core (F : G ⥤ C) : G ⥤ core C :=
{ obj := λ X, lift (F.obj X),
  map := λ X Y f, ⟨F.map f, F.map (inv f)⟩ }

def forget_functor_to_core : (G ⥤ core C) ⥤ (G ⥤ C) := (whiskering_right _ _ _).obj inclusion
end core

/--
`of_equiv_functor m` lifts a type-level `equiv_functor`
to a categorical functor `core (Type u₁) ⥤ core (Type u₂)`.
-/
def of_equiv_functor (m : Type u₁ → Type u₂) [equiv_functor m] :
  core (Type u₁) ⥤ core (Type u₂) :=
{ obj       := λ α, lift (m (desc α)),
  map       := λ α β f, (equiv_functor.map_equiv m f.to_equiv).to_iso,
  -- These are not very pretty.
  map_id' := λ α, begin ext, exact (congr_fun (equiv_functor.map_refl _) x), end,
  map_comp' := λ α β γ f g,
  begin
    ext,
    simp only [equiv_functor.map_equiv_apply, equiv.to_iso_hom,
      function.comp_app, core.comp_hom, types_comp],
    erw [iso.to_equiv_comp, equiv_functor.map_trans],
  end, }

end category_theory
