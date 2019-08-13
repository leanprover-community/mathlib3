/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import category_theory.functor

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

@[simp] lemma trans_mk {X Y Z : C}
  (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id)
  (hom' : Y ⟶ Z) (inv' : Z ⟶ Y) (hom_inv_id') (inv_hom_id') (hom_inv_id'') (inv_hom_id'') :
  iso.trans
    {hom := hom, inv := inv, hom_inv_id' := hom_inv_id, inv_hom_id' := inv_hom_id}
    {hom := hom', inv := inv', hom_inv_id' := hom_inv_id', inv_hom_id' := inv_hom_id'} =
  {hom := hom ≫ hom', inv := inv' ≫ inv, hom_inv_id' := hom_inv_id'', inv_hom_id' := inv_hom_id''} :=
rfl

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

variables {f g : X ⟶ Y} {h : Y ⟶ Z}

instance inv_is_iso [is_iso f] : is_iso (category_theory.inv f) :=
{ inv := f,
  hom_inv_id' := inv_hom_id f,
  inv_hom_id' := hom_inv_id f }
instance comp_is_iso [is_iso f] [is_iso h] : is_iso (f ≫ h) :=
{ inv := category_theory.inv h ≫ category_theory.inv f,
  hom_inv_id' := begin erw [category.assoc, hom_inv_id_assoc], exact hom_inv_id f, end,
  inv_hom_id' := begin erw [category.assoc, inv_hom_id_assoc], exact inv_hom_id h, end }

@[simp] lemma inv_id : category_theory.inv (𝟙 X) = 𝟙 X := rfl
@[simp] lemma inv_comp [is_iso f] [is_iso h] :
  category_theory.inv (f ≫ h) = category_theory.inv h ≫ category_theory.inv f := rfl
@[simp] lemma is_iso.inv_inv [is_iso f] : category_theory.inv (category_theory.inv f) = f := rfl
@[simp] lemma iso.inv_inv (f : X ≅ Y) :
  category_theory.inv (f.inv) = f.hom := rfl
@[simp] lemma iso.inv_hom (f : X ≅ Y) :
  category_theory.inv (f.hom) = f.inv := rfl

instance epi_of_iso (f : X ⟶ Y) [is_iso f] : epi f  :=
{ left_cancellation := λ Z g h w,
  -- This is an interesting test case for better rewrite automation.
  by rw [←category.id_comp C g, ←category.id_comp C h, ←is_iso.inv_hom_id f, category.assoc, w, category.assoc] }
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

def as_iso (f : X ⟶ Y) [is_iso f] : X ≅ Y :=
{ hom := f, inv := inv f }

@[simp] lemma as_iso_hom (f : X ⟶ Y) [is_iso f] : (as_iso f).hom = f := rfl
@[simp] lemma as_iso_inv (f : X ⟶ Y) [is_iso f] : (as_iso f).inv = inv f := rfl

instance (f : X ⟶ Y) : subsingleton (is_iso f) :=
⟨λ a b,
 suffices a.inv = b.inv, by cases a; cases b; congr; exact this,
 show (@as_iso C _ _ _ f a).inv = (@as_iso C _ _ _ f b).inv,
 by congr' 1; ext; refl⟩

lemma is_iso.inv_eq_inv {f g : X ⟶ Y} [is_iso f] [is_iso g] : inv f = inv g ↔ f = g :=
iso.inv_eq_inv (as_iso f) (as_iso g)

instance is_iso_comp (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso f] [is_iso g] : is_iso (f ≫ g) :=
{ inv := inv g ≫ inv f }

instance is_iso_id : is_iso (𝟙 X) := { inv := 𝟙 X }

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

@[simp] lemma map_iso_trans (F : C ⥤ D) {X Y Z : C} (i : X ≅ Y) (j : Y ≅ Z) :
  F.map_iso (i ≪≫ j) = (F.map_iso i) ≪≫ (F.map_iso j) :=
by ext; apply functor.map_comp

instance (F : C ⥤ D) (f : X ⟶ Y) [is_iso f] : is_iso (F.map f) :=
{ ..(F.map_iso (as_iso f)) }

@[simp] lemma map_hom_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [is_iso f] :
  F.map f ≫ F.map (inv f) = 𝟙 (F.obj X) :=
by rw [←map_comp, is_iso.hom_inv_id, map_id]

@[simp] lemma map_inv_hom (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [is_iso f] :
  F.map (inv f) ≫ F.map f = 𝟙 (F.obj Y) :=
by rw [←map_comp, is_iso.inv_hom_id, map_id]

@[simp] lemma map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [is_iso f] : F.map (inv f) = inv (F.map f) := rfl

end functor

end category_theory
