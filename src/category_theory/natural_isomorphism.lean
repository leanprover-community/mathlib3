/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import category_theory.functor_category
import category_theory.isomorphism

open category_theory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace category_theory
open nat_trans

/-- The application of a natural isomorphism to an object. We put this definition in a different
namespace, so that we can use `α.app` -/
@[simp, reducible] def iso.app {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
  {F G : C ⥤ D} (α : F ≅ G) (X : C) : F.obj X ≅ G.obj X :=
{ hom := α.hom.app X,
  inv := α.inv.app X,
  hom_inv_id' := begin rw [← comp_app, iso.hom_inv_id], refl end,
  inv_hom_id' := begin rw [← comp_app, iso.inv_hom_id], refl end }


namespace nat_iso

open category_theory.category category_theory.functor

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
  {E : Type u₃} [category.{v₃} E]

@[simp] lemma trans_app {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) (X : C) :
  (α ≪≫ β).app X = α.app X ≪≫ β.app X := rfl

lemma app_hom {F G : C ⥤ D} (α : F ≅ G) (X : C) : (α.app X).hom = α.hom.app X := rfl
lemma app_inv {F G : C ⥤ D} (α : F ≅ G) (X : C) : (α.app X).inv = α.inv.app X := rfl

@[simp, reassoc]
lemma hom_inv_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
  α.hom.app X ≫ α.inv.app X = 𝟙 (F.obj X) :=
congr_fun (congr_arg app α.hom_inv_id) X

@[simp, reassoc]
lemma inv_hom_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
  α.inv.app X ≫ α.hom.app X = 𝟙 (G.obj X) :=
congr_fun (congr_arg app α.inv_hom_id) X

variables {F G : C ⥤ D}

instance hom_app_is_iso (α : F ≅ G) (X : C) : is_iso (α.hom.app X) :=
{ inv := α.inv.app X,
  hom_inv_id' := begin rw [←comp_app, iso.hom_inv_id, ←id_app] end,
  inv_hom_id' := begin rw [←comp_app, iso.inv_hom_id, ←id_app] end }
instance inv_app_is_iso (α : F ≅ G) (X : C) : is_iso (α.inv.app X) :=
{ inv := α.hom.app X,
  hom_inv_id' := begin rw [←comp_app, iso.inv_hom_id, ←id_app] end,
  inv_hom_id' := begin rw [←comp_app, iso.hom_inv_id, ←id_app] end }

lemma hom_app_inv_app_id (α : F ≅ G) (X : C) : α.hom.app X ≫ α.inv.app X = 𝟙 _ :=
hom_inv_id_app _ _
lemma inv_app_hom_app_id (α : F ≅ G) (X : C) : α.inv.app X ≫ α.hom.app X = 𝟙 _ :=
inv_hom_id_app _ _

variables {X Y : C}
lemma naturality_1 (α : F ≅ G) (f : X ⟶ Y) :
  (α.inv.app X) ≫ (F.map f) ≫ (α.hom.app Y) = G.map f :=
begin erw [naturality, ←category.assoc, is_iso.hom_inv_id, category.id_comp] end
lemma naturality_2 (α : F ≅ G) (f : X ⟶ Y) :
  (α.hom.app X) ≫ (G.map f) ≫ (α.inv.app Y) = F.map f :=
begin erw [naturality, ←category.assoc, is_iso.hom_inv_id, category.id_comp] end

def is_iso_of_is_iso_app (α : F ⟶ G) [∀ X : C, is_iso (α.app X)] : is_iso α :=
{ inv :=
  { app := λ X, inv (α.app X),
    naturality' := λ X Y f,
     begin
       have h := congr_arg (λ f, inv (α.app X) ≫ (f ≫ inv (α.app Y))) (α.naturality f).symm,
       simp only [is_iso.inv_hom_id_assoc, is_iso.hom_inv_id, assoc, comp_id, cancel_mono] at h,
       exact h
     end } }

instance is_iso_of_is_iso_app' (α : F ⟶ G) [H : ∀ X : C, is_iso (nat_trans.app α X)] : is_iso α :=
@nat_iso.is_iso_of_is_iso_app _ _ _ _ _ _ α H

-- TODO can we make this an instance?
def is_iso_app_of_is_iso (α : F ⟶ G) [is_iso α] (X) : is_iso (α.app X) :=
{ inv := (inv α).app X,
  hom_inv_id' := congr_fun (congr_arg nat_trans.app (is_iso.hom_inv_id α)) X,
  inv_hom_id' := congr_fun (congr_arg nat_trans.app (is_iso.inv_hom_id α)) X }

def of_components (app : ∀ X : C, F.obj X ≅ G.obj X)
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f) :
  F ≅ G :=
as_iso { app := λ X, (app X).hom }

@[simp] lemma of_components.app (app' : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X) :
  (of_components app' naturality).app X = app' X :=
by tidy
@[simp] lemma of_components.hom_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X) :
  (of_components app naturality).hom.app X = (app X).hom := rfl
@[simp] lemma of_components.inv_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X) :
  (of_components app naturality).inv.app X = (app X).inv := rfl

def hcomp {F G : C ⥤ D} {H I : D ⥤ E} (α : F ≅ G) (β : H ≅ I) : F ⋙ H ≅ G ⋙ I :=
begin
  refine ⟨α.hom ◫ β.hom, α.inv ◫ β.inv, _, _⟩,
  { ext, rw [←nat_trans.exchange], simp, refl },
  ext, rw [←nat_trans.exchange], simp, refl
end
-- declare local notation for nat_iso.hcomp
localized "infix ` ■ `:80 := category_theory.nat_iso.hcomp" in category


end nat_iso

namespace functor

variables {C : Type u₁} [category.{v₁} C]

def ulift_down_up : ulift_down.{v₁} C ⋙ ulift_up C ≅ 𝟭 (ulift.{u₂} C) :=
{ hom := { app := λ X, @category_struct.id (ulift.{u₂} C) _ X },
  inv := { app := λ X, @category_struct.id (ulift.{u₂} C) _ X } }

def ulift_up_down : ulift_up.{v₁} C ⋙ ulift_down C ≅ 𝟭 C :=
{ hom := { app := λ X, 𝟙 X },
  inv := { app := λ X, 𝟙 X } }


end functor
end category_theory
