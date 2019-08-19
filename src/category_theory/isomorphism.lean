/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import category_theory.functor

/-!
# Isomorphisms

This file defines isomorphisms between objects of a category.

## Main definitions

- `structure iso` : a bundled isomorphism between two objects of a category;
- `class is_iso` : an unbundled version of `iso`; note that `is_iso f` is usually *not* a `Prop`,
  because it holds the inverse morphism;
- `as_iso` : convert from `is_iso` to `iso`;
- `of_iso` : convert from `iso` to `is_iso`;
- standard operations on isomorphisms (composition, inverse etc)

## Notations

- `X ≅ Y` : same as `iso X Y`;
- `α ≪≫ β` : composition of two isomorphisms; it is called `iso.trans`

## Tags

category, category theory, isomorphism
-/

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory
open category

structure iso {C : Type u} [category.{v} C] (X Y : C) :=
(hom : X ⟶ Y)
(inv : Y ⟶ X)
(hom_inv_id' : hom ≫ inv = 𝟙 X . obviously)
(inv_hom_id' : inv ≫ hom = 𝟙 Y . obviously)

restate_axiom iso.hom_inv_id'
restate_axiom iso.inv_hom_id'
attribute [simp] iso.hom_inv_id iso.inv_hom_id

infixr ` ≅ `:10  := iso             -- type as \cong or \iso

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
variables {X Y Z : C}

namespace iso

@[simp] lemma hom_inv_id_assoc (α : X ≅ Y) (f : X ⟶ Z) : α.hom ≫ α.inv ≫ f = f :=
by rw [←category.assoc, α.hom_inv_id, category.id_comp]

@[simp] lemma inv_hom_id_assoc (α : X ≅ Y) (f : Y ⟶ Z) : α.inv ≫ α.hom ≫ f = f :=
by rw [←category.assoc, α.inv_hom_id, category.id_comp]

@[extensionality] lemma ext (α β : X ≅ Y) (w : α.hom = β.hom) : α = β :=
suffices α.inv = β.inv, by cases α; cases β; cc,
calc α.inv
    = α.inv ≫ (β.hom ≫ β.inv) : by rw [iso.hom_inv_id, category.comp_id]
... = (α.inv ≫ α.hom) ≫ β.inv : by rw [category.assoc, ←w]
... = β.inv                   : by rw [iso.inv_hom_id, category.id_comp]

@[symm] def symm (I : X ≅ Y) : Y ≅ X :=
{ hom := I.inv,
  inv := I.hom,
  hom_inv_id' := I.inv_hom_id',
  inv_hom_id' := I.hom_inv_id' }

@[simp] lemma symm_hom (α : X ≅ Y) : α.symm.hom = α.inv := rfl
@[simp] lemma symm_inv (α : X ≅ Y) : α.symm.inv = α.hom := rfl

@[simp] lemma symm_mk {X Y : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id) :
  iso.symm {hom := hom, inv := inv, hom_inv_id' := hom_inv_id, inv_hom_id' := inv_hom_id} =
    {hom := inv, inv := hom, hom_inv_id' := inv_hom_id, inv_hom_id' := hom_inv_id} := rfl

@[simp] lemma symm_symm_eq {X Y : C} (α : X ≅ Y) : α.symm.symm = α :=
by cases α; refl

@[simp] lemma symm_eq_iff {X Y : C} {α β : X ≅ Y} : α.symm = β.symm ↔ α = β :=
⟨λ h, symm_symm_eq α ▸ symm_symm_eq β ▸ congr_arg symm h, congr_arg symm⟩

@[refl] def refl (X : C) : X ≅ X :=
{ hom := 𝟙 X,
  inv := 𝟙 X }

@[simp] lemma refl_hom (X : C) : (iso.refl X).hom = 𝟙 X := rfl
@[simp] lemma refl_inv (X : C) : (iso.refl X).inv = 𝟙 X := rfl
@[simp] lemma refl_symm (X : C) : (iso.refl X).symm = iso.refl X := rfl

@[trans] def trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z :=
{ hom := α.hom ≫ β.hom,
  inv := β.inv ≫ α.inv }

infixr ` ≪≫ `:80 := iso.trans -- type as `\ll \gg`.

@[simp] lemma trans_hom (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).hom = α.hom ≫ β.hom := rfl
@[simp] lemma trans_inv (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).inv = β.inv ≫ α.inv := rfl

@[simp] lemma trans_mk {X Y Z : C}
  (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id)
  (hom' : Y ⟶ Z) (inv' : Z ⟶ Y) (hom_inv_id') (inv_hom_id') (hom_inv_id'') (inv_hom_id'') :
  iso.trans
    {hom := hom, inv := inv, hom_inv_id' := hom_inv_id, inv_hom_id' := inv_hom_id}
    {hom := hom', inv := inv', hom_inv_id' := hom_inv_id', inv_hom_id' := inv_hom_id'} =
  {hom := hom ≫ hom', inv := inv' ≫ inv, hom_inv_id' := hom_inv_id'', inv_hom_id' := inv_hom_id''} :=
rfl

@[simp] lemma trans_symm (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).symm = β.symm ≪≫ α.symm := rfl
@[simp] lemma trans_assoc {Z' : C} (α : X ≅ Y) (β : Y ≅ Z) (γ : Z ≅ Z') :
  (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ :=
by ext; simp only [trans_hom, category.assoc]

@[simp] lemma refl_trans (α : X ≅ Y) : (iso.refl X) ≪≫ α = α := by ext; apply category.id_comp
@[simp] lemma trans_refl (α : X ≅ Y) : α ≪≫ (iso.refl Y) = α := by ext; apply category.comp_id

@[simp] lemma symm_self_id (α : X ≅ Y) : α.symm ≪≫ α = iso.refl Y := ext _ _ α.inv_hom_id
@[simp] lemma self_symm_id (α : X ≅ Y) : α ≪≫ α.symm = iso.refl X := ext _ _ α.hom_inv_id

@[simp] lemma symm_self_id_assoc (α : X ≅ Y) (β : Y ≅ Z) : α.symm ≪≫ α ≪≫ β = β :=
by rw [← trans_assoc, symm_self_id, refl_trans]

@[simp] lemma self_symm_id_assoc (α : X ≅ Y) (β : X ≅ Z) : α ≪≫ α.symm ≪≫ β = β :=
by rw [← trans_assoc, self_symm_id, refl_trans]

lemma inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g :=
⟨λ H, by simp [H.symm], λ H, by simp [H]⟩

lemma eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f :=
(inv_comp_eq α.symm).symm

lemma comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom :=
⟨λ H, by simp [H.symm], λ H, by simp [H]⟩

lemma eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f :=
(comp_inv_eq α.symm).symm

lemma inv_eq_inv (f g : X ≅ Y) : f.inv = g.inv ↔ f.hom = g.hom :=
have ∀{X Y : C} (f g : X ≅ Y), f.hom = g.hom → f.inv = g.inv, from λ X Y f g h, by rw [ext _ _ h],
⟨this f.symm g.symm, this f g⟩

lemma hom_comp_eq_id (α : X ≅ Y) {f : Y ⟶ X} : α.hom ≫ f = 𝟙 X ↔ f = α.inv :=
by rw [←eq_inv_comp, comp_id]

lemma comp_hom_eq_id (α : X ≅ Y) {f : Y ⟶ X} : f ≫ α.hom = 𝟙 Y ↔ f = α.inv :=
by rw [←eq_comp_inv, id_comp]

lemma hom_eq_inv (α : X ≅ Y) (β : Y ≅ X) : α.hom = β.inv ↔ β.hom = α.inv :=
by { erw [inv_eq_inv α.symm β, eq_comm], refl }

end iso

/-- `is_iso` typeclass expressing that a morphism is invertible.
    This contains the data of the inverse, but is a subsingleton type. -/
class is_iso (f : X ⟶ Y) :=
(inv : Y ⟶ X)
(hom_inv_id' : f ≫ inv = 𝟙 X . obviously)
(inv_hom_id' : inv ≫ f = 𝟙 Y . obviously)

export is_iso (inv)

def as_iso (f : X ⟶ Y) [h : is_iso f] : X ≅ Y := { hom := f, ..h }

@[simp] lemma as_iso_hom (f : X ⟶ Y) [is_iso f] : (as_iso f).hom = f := rfl
@[simp] lemma as_iso_inv (f : X ⟶ Y) [is_iso f] : (as_iso f).inv = inv f := rfl

namespace is_iso

@[simp] lemma hom_inv_id (f : X ⟶ Y) [is_iso f] : f ≫ inv f = 𝟙 X :=
is_iso.hom_inv_id' f
@[simp] lemma inv_hom_id (f : X ⟶ Y) [is_iso f] : inv f ≫ f = 𝟙 Y :=
is_iso.inv_hom_id' f

@[simp] lemma hom_inv_id_assoc {Z} (f : X ⟶ Y) [is_iso f] (g : X ⟶ Z) :
  f ≫ inv f ≫ g = g :=
(as_iso f).hom_inv_id_assoc g

@[simp] lemma inv_hom_id_assoc {Z} (f : X ⟶ Y) [is_iso f] (g : Y ⟶ Z) :
  inv f ≫ f ≫ g = g :=
(as_iso f).inv_hom_id_assoc g

instance (X : C) : is_iso (𝟙 X) :=
{ inv := 𝟙 X }

instance of_iso (f : X ≅ Y) : is_iso f.hom :=
{ .. f }

instance of_iso_inverse (f : X ≅ Y) : is_iso f.inv :=
is_iso.of_iso f.symm

variables {f g : X ⟶ Y} {h : Y ⟶ Z}

instance inv_is_iso [is_iso f] : is_iso (inv f) :=
is_iso.of_iso_inverse (as_iso f)

instance comp_is_iso [is_iso f] [is_iso h] : is_iso (f ≫ h) :=
is_iso.of_iso $ (as_iso f) ≪≫ (as_iso h)

@[simp] lemma inv_id : inv (𝟙 X) = 𝟙 X := rfl
@[simp] lemma inv_comp [is_iso f] [is_iso h] : inv (f ≫ h) = inv h ≫ inv f := rfl
@[simp] lemma is_iso.inv_inv [is_iso f] : inv (inv f) = f := rfl
@[simp] lemma iso.inv_inv (f : X ≅ Y) : inv (f.inv) = f.hom := rfl
@[simp] lemma iso.inv_hom (f : X ≅ Y) : inv (f.hom) = f.inv := rfl

instance epi_of_iso (f : X ⟶ Y) [is_iso f] : epi f  :=
{ left_cancellation := λ Z g h w,
  -- This is an interesting test case for better rewrite automation.
  by rw [← is_iso.inv_hom_id_assoc f g, w, is_iso.inv_hom_id_assoc f h] }
instance mono_of_iso (f : X ⟶ Y) [is_iso f] : mono f :=
{ right_cancellation := λ Z g h w,
  by rw [←category.comp_id C g, ←category.comp_id C h, ←is_iso.hom_inv_id f, ←category.assoc, w, ←category.assoc] }

end is_iso

open is_iso

lemma eq_of_inv_eq_inv {f g : X ⟶ Y} [is_iso f] [is_iso g] (p : inv f = inv g) : f = g :=
begin
  apply (cancel_epi (inv f)).1,
  erw [inv_hom_id, p, inv_hom_id],
end

instance (f : X ⟶ Y) : subsingleton (is_iso f) :=
⟨λ a b,
 suffices a.inv = b.inv, by cases a; cases b; congr; exact this,
 show (@as_iso C _ _ _ f a).inv = (@as_iso C _ _ _ f b).inv,
 by congr' 1; ext; refl⟩

lemma is_iso.inv_eq_inv {f g : X ⟶ Y} [is_iso f] [is_iso g] : inv f = inv g ↔ f = g :=
iso.inv_eq_inv (as_iso f) (as_iso g)

namespace functor

universes u₁ v₁ u₂ v₂
variables {D : Type u₂}

variables [𝒟 : category.{v₂} D]
include 𝒟

def map_iso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.obj X ≅ F.obj Y :=
{ hom := F.map i.hom,
  inv := F.map i.inv,
  hom_inv_id' := by rw [←map_comp, iso.hom_inv_id, ←map_id],
  inv_hom_id' := by rw [←map_comp, iso.inv_hom_id, ←map_id] }

@[simp] lemma map_iso_hom (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : (F.map_iso i).hom = F.map i.hom := rfl
@[simp] lemma map_iso_inv (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : (F.map_iso i).inv = F.map i.inv := rfl

@[simp] lemma map_iso_symm (F : C ⥤ D) {X Y : C} (i : X ≅ Y) :
  F.map_iso i.symm = (F.map_iso i).symm :=
rfl

@[simp] lemma map_iso_trans (F : C ⥤ D) {X Y Z : C} (i : X ≅ Y) (j : Y ≅ Z) :
  F.map_iso (i ≪≫ j) = (F.map_iso i) ≪≫ (F.map_iso j) :=
by ext; apply functor.map_comp

instance map_is_iso (F : C ⥤ D) (f : X ⟶ Y) [is_iso f] : is_iso (F.map f) :=
is_iso.of_iso $ F.map_iso (as_iso f)

@[simp] lemma map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [is_iso f] :
  F.map (inv f) = inv (F.map f) :=
rfl

@[simp] lemma map_hom_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [is_iso f] :
  F.map f ≫ F.map (inv f) = 𝟙 (F.obj X) :=
by rw [map_inv, is_iso.hom_inv_id]

@[simp] lemma map_inv_hom (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [is_iso f] :
  F.map (inv f) ≫ F.map f = 𝟙 (F.obj Y) :=
by rw [map_inv, is_iso.inv_hom_id]

end functor

end category_theory
