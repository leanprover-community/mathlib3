-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.products
import category_theory.types

namespace category_theory

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

def opposite (C : Type u₁) : Type u₁ := C

-- Use a high right binding power (like that of postfix ⁻¹) so that, for example,
-- `presheaf Cᵒᵖ` parses as `presheaf (Cᵒᵖ)` and not `(presheaf C)ᵒᵖ`.
notation C `ᵒᵖ`:std.prec.max_plus := opposite C

variables {C : Type u₁}

def op (X : C) : Cᵒᵖ := X
def unop (X : Cᵒᵖ) : C := X
@[simp] lemma unop_op (X : C) : unop (op X) = X := rfl
@[simp] lemma op_unop (X : Cᵒᵖ) : op (unop X) = X := rfl

variables (C) [𝒞 : category.{v₁} C]
include 𝒞

instance opposite_category : category.{v₁} (Cᵒᵖ) :=
{ hom  := λ X Y : Cᵒᵖ, (unop Y) ⟶ (unop X),
  comp := λ _ _ _ f g, g ≫ f,
  id   := λ X, 𝟙 (unop X) }

namespace category.hom
variables {C}
def op {X Y : C} (f : X ⟶ Y) : (op Y) ⟶ (op X) := f
def unop {X Y : Cᵒᵖ} (f : X ⟶ Y) : (unop Y) ⟶ (unop X) := f

@[simp] lemma op_id (X : C) : op (𝟙 X) = 𝟙 (category_theory.op X) := rfl
@[simp] lemma unop_id (X : Cᵒᵖ) : unop (𝟙 X) = 𝟙 (category_theory.unop X) := rfl
@[simp] lemma comp_op_op {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (op g) ≫ (op f) = op (f ≫ g) := rfl
@[simp] lemma comp_unop {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
  unop (f ≫ g) = (unop g) ≫ (unop f) := rfl

@[simp] lemma op_unop {X Y : C} (f : X ⟶ Y) : f.op.unop = f := rfl
@[simp] lemma unop_op {X Y : Cᵒᵖ} (f : X ⟶ Y) : f.unop.op = f := rfl

attribute [irreducible] op unop
end category.hom

section
def op_op : (Cᵒᵖ)ᵒᵖ ⥤ C :=
{ obj := λ X, unop (unop X),
  map := λ X Y f, f }
end

variables {C}

namespace functor

section
local attribute [semireducible] category.hom.op category.hom.unop

variables {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒟

variables {C D}

protected def op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ :=
{ obj       := λ X, op (F.obj (unop X)),
  map       := λ X Y f, (F.map f.unop).op,
  map_id'   := by intros; erw [map_id]; refl,
  map_comp' := by intros; erw [map_comp]; refl }

@[simp] lemma op' (F : C ⥤ D) (X : Cᵒᵖ) :
  (F.op).obj X = op (F.obj (unop X)) := rfl
@[simp] lemma op_map' (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
  (F.op).map f = (F.map f.unop).op := rfl

protected def unop (F : Cᵒᵖ ⥤ Dᵒᵖ) : C ⥤ D :=
{ obj       := λ X, unop (F.obj (op X)),
  map       := λ X Y f, (F.map f.op).unop,
  map_id'   := by intros; erw [map_id]; refl,
  map_comp' := by intros; erw [map_comp]; refl }

@[simp] lemma unop' (F : Cᵒᵖ ⥤ Dᵒᵖ) (X : C) :
  (F.unop).obj X = unop (F.obj (op X)) := rfl
@[simp] lemma unop_map' (F : Cᵒᵖ ⥤ Dᵒᵖ) {X Y : C} (f : X ⟶ Y) :
  (F.unop).map f = (F.map f.op).unop := rfl

variables (C D)

def op_hom : (C ⥤ D)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Dᵒᵖ) :=
{ obj := λ F, (unop F).op,
  map := λ F G α,
  { app := λ X, α.app (unop X),
    naturality' := λ X Y f, eq.symm (α.naturality f) } }

@[simp] lemma op_hom.obj (F : (C ⥤ D)ᵒᵖ) : (op_hom C D).obj F = (unop F).op := rfl
@[simp] lemma op_hom.map_app {F G : (C ⥤ D)ᵒᵖ} (α : F ⟶ G) (X : Cᵒᵖ) :
  ((op_hom C D).map α).app X = α.app (unop X) := rfl

def op_inv : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (C ⥤ D)ᵒᵖ :=
{ obj := λ F, op F.unop,
  map := λ F G α,
  { app := λ X, α.app (op X),
    naturality' := λ X Y f, eq.symm (α.naturality f) } }

@[simp] lemma op_inv.obj (F : Cᵒᵖ ⥤ Dᵒᵖ) : (op_inv C D).obj F = op F.unop := rfl
@[simp] lemma op_inv.map_app {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) (X : C) :
  ((op_inv C D).map α).app X = α.app (op X) := rfl

instance {F : C ⥤ D} [full F] : full F.op :=
{ preimage := λ X Y f, (F.preimage f.unop).op }

instance {F : C ⥤ D} [faithful F] : faithful F.op :=
{ injectivity' := λ X Y f g h, by simpa using injectivity F h }

@[simp] lemma preimage_id (F : C ⥤ D) [fully_faithful F] (X : C) : F.preimage (𝟙 (F.obj X)) = 𝟙 X :=
injectivity F (by simp)

end

section
def op_iso {X Y : C} (f : X ≅ Y) : (op X) ≅ (op Y) :=
{ hom := f.inv.op,
  inv := f.hom.op }

@[simp] lemma op_iso_hom {X Y : C} (f : X ≅ Y) : (op_iso f).hom = f.inv.op := rfl
@[simp] lemma op_iso_inv {X Y : C} (f : X ≅ Y) : (op_iso f).inv = f.hom.op := rfl
end

section

variable (C)

/-- `functor.hom` is the hom-pairing, sending (X,Y) to X → Y, contravariant in X and covariant in Y. -/
def hom : (Cᵒᵖ × C) ⥤ (Type v₁) :=
{ obj       := λ X, (unop X.1) ⟶ X.2,
  map       := λ X Y f, λ h, f.1 ≫ h ≫ f.2,
  map_id'   := begin intros, ext, dsimp [category_theory.opposite_category], simp end,
  map_comp' := begin intros, ext, dsimp [category_theory.opposite_category], simp end }

@[simp] lemma hom_obj (X : Cᵒᵖ × C) : (functor.hom C).obj X = ((unop X.1) ⟶ X.2) := rfl
@[simp] lemma hom_pairing_map {X Y : Cᵒᵖ × C} (f : X ⟶ Y) :
  (functor.hom C).map f = λ h, f.1 ≫ h ≫ f.2 := rfl

end

end functor

end category_theory
