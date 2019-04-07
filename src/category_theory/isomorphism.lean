-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import category_theory.functor

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory

structure iso {C : Sort u} [category.{v} C] (X Y : C) :=
(hom : X ⟶ Y)
(inv : Y ⟶ X)
(hom_inv_id' : hom ≫ inv = 𝟙 X . obviously)
(inv_hom_id' : inv ≫ hom = 𝟙 Y . obviously)

restate_axiom iso.hom_inv_id'
restate_axiom iso.inv_hom_id'
attribute [simp] iso.hom_inv_id iso.inv_hom_id

infixr ` ≅ `:10  := iso             -- type as \cong or \iso

variables {C : Sort u} [𝒞 : category.{v} C]
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

@[refl] def refl (X : C) : X ≅ X :=
{ hom := 𝟙 X,
  inv := 𝟙 X }

@[simp] lemma refl_hom (X : C) : (iso.refl X).hom = 𝟙 X := rfl
@[simp] lemma refl_inv (X : C) : (iso.refl X).inv = 𝟙 X := rfl

@[trans] def trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z :=
{ hom := α.hom ≫ β.hom,
  inv := β.inv ≫ α.inv }

infixr ` ≪≫ `:80 := iso.trans -- type as `\ll \gg`.

@[simp] lemma trans_hom (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).hom = α.hom ≫ β.hom := rfl
@[simp] lemma trans_inv (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).inv = β.inv ≫ α.inv := rfl

@[simp] lemma refl_symm (X : C) : (iso.refl X).hom = 𝟙 X := rfl
@[simp] lemma trans_symm (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).inv = β.inv ≫ α.inv := rfl

lemma inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g :=
⟨λ H, by simp [H.symm], λ H, by simp [H]⟩

lemma eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f :=
(inv_comp_eq α.symm).symm

lemma comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom :=
⟨λ H, by simp [H.symm], λ H, by simp [H]⟩

lemma eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f :=
(comp_inv_eq α.symm).symm

end iso

/-- `is_iso` typeclass expressing that a morphism is invertible.
    This contains the data of the inverse, but is a subsingleton type. -/
class is_iso (f : X ⟶ Y) :=
(inv : Y ⟶ X)
(hom_inv_id' : f ≫ inv = 𝟙 X . obviously)
(inv_hom_id' : inv ≫ f = 𝟙 Y . obviously)

def inv (f : X ⟶ Y) [is_iso f] := is_iso.inv f

namespace is_iso

@[simp] lemma hom_inv_id (f : X ⟶ Y) [is_iso f] : f ≫ category_theory.inv f = 𝟙 X :=
is_iso.hom_inv_id' f
@[simp] lemma inv_hom_id (f : X ⟶ Y) [is_iso f] : category_theory.inv f ≫ f = 𝟙 Y :=
is_iso.inv_hom_id' f

@[simp] lemma hom_inv_id_assoc {Z} (f : X ⟶ Y) [is_iso f] (g : X ⟶ Z) : f ≫ category_theory.inv f ≫ g = g :=
by rw [←category.assoc, hom_inv_id, category.id_comp]
@[simp] lemma inv_hom_id_assoc {Z} (f : X ⟶ Y) [is_iso f] (g : Y ⟶ Z) : category_theory.inv f ≫ f ≫ g = g :=
by rw [←category.assoc, inv_hom_id, category.id_comp]

instance (X : C) : is_iso (𝟙 X) :=
{ inv := 𝟙 X }

instance of_iso (f : X ≅ Y) : is_iso f.hom :=
{ inv := f.inv }
instance of_iso_inverse (f : X ≅ Y) : is_iso f.inv :=
{ inv := f.hom }

end is_iso

def as_iso (f : X ⟶ Y) [is_iso f] : X ≅ Y :=
{ hom := f, inv := inv f }

@[simp] lemma as_iso_hom (f : X ⟶ Y) [is_iso f] : (as_iso f).hom = f := rfl
@[simp] lemma as_iso_inv (f : X ⟶ Y) [is_iso f] : (as_iso f).inv = inv f := rfl

instance (f : X ⟶ Y) : subsingleton (is_iso f) :=
⟨λ a b,
 suffices a.inv = b.inv, by cases a; cases b; congr; exact this,
 show (@as_iso C _ _ _ f a).inv = (@as_iso C _ _ _ f b).inv,
 by congr' 1; ext; refl⟩

namespace functor

universes u₁ v₁ u₂ v₂
variables {D : Sort u₂}

variables [𝒟 : category.{v₂} D]
include 𝒟

def on_iso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.obj X ≅ F.obj Y :=
{ hom := F.map i.hom,
  inv := F.map i.inv,
  hom_inv_id' := by rw [←map_comp, iso.hom_inv_id, ←map_id],
  inv_hom_id' := by rw [←map_comp, iso.inv_hom_id, ←map_id] }

@[simp] lemma on_iso_hom (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : (F.on_iso i).hom = F.map i.hom := rfl
@[simp] lemma on_iso_inv (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : (F.on_iso i).inv = F.map i.inv := rfl

instance (F : C ⥤ D) (f : X ⟶ Y) [is_iso f] : is_iso (F.map f) :=
{ inv := F.map (inv f),
  hom_inv_id' := by rw [← F.map_comp, is_iso.hom_inv_id, map_id],
  inv_hom_id' := by rw [← F.map_comp, is_iso.inv_hom_id, map_id] }

@[simp] lemma map_hom_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [is_iso f] :
  F.map f ≫ F.map (inv f) = 𝟙 (F.obj X) :=
begin
  rw [←map_comp, is_iso.hom_inv_id, map_id],
end
@[simp] lemma map_inv_hom (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [is_iso f] :
  F.map (inv f) ≫ F.map f = 𝟙 (F.obj Y) :=
begin
  rw [←map_comp, is_iso.inv_hom_id, map_id],
end

end functor

instance epi_of_iso  (f : X ⟶ Y) [is_iso f] : epi f  :=
{ left_cancellation := begin
                         -- This is an interesting test case for better rewrite automation.
                         intros,
                         rw [←category.id_comp C g, ←category.id_comp C h],
                         rw [← is_iso.inv_hom_id f],
                         rw [category.assoc, w, category.assoc],
                       end }
instance mono_of_iso (f : X ⟶ Y) [is_iso f] : mono f :=
{ right_cancellation := begin
                         intros,
                         rw [←category.comp_id C g, ←category.comp_id C h],
                         rw [← is_iso.hom_inv_id f],
                         rw [←category.assoc, w, ←category.assoc]
                       end }

end category_theory

namespace category_theory

 -- We need to get the morphism universe level up into `Type`, in order to have group structures.
variables {C : Sort u} [𝒞 : category.{v+1} C]
include 𝒞

def Aut (X : C) := X ≅ X

attribute [extensionality Aut] iso.ext

instance {X : C} : group (Aut X) :=
by refine { one := iso.refl X,
            inv := iso.symm,
            mul := iso.trans, .. } ; obviously

end category_theory
