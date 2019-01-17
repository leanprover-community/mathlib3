-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.products
import category_theory.types

namespace category_theory

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

def op (C : Type u₁) : Type u₁ := C

-- Use a high right binding power (like that of postfix ⁻¹) so that, for example,
-- `presheaf Cᵒᵖ` parses as `presheaf (Cᵒᵖ)` and not `(presheaf C)ᵒᵖ`.
notation C `ᵒᵖ`:std.prec.max_plus := op C

variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

instance opposite : category.{v₁} Cᵒᵖ :=
{ hom  := λ X Y : C, Y ⟶ X,
  comp := λ _ _ _ f g, g ≫ f,
  id   := λ X, 𝟙 X }

def op_op : (Cᵒᵖ)ᵒᵖ ⥤ C :=
{ obj := λ X, X,
  map := λ X Y f, f }

-- TODO this is an equivalence

namespace functor

section

variables {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒟

variables {C D}

protected definition op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ :=
{ obj       := λ X, F.obj X,
  map       := λ X Y f, F.map f,
  map_id'   := begin /- `obviously'` says: -/ intros, erw [map_id], refl, end,
  map_comp' := begin /- `obviously'` says: -/ intros, erw [map_comp], refl end }

@[simp] lemma op_obj (F : C ⥤ D) (X : C) : (F.op).obj X = F.obj X := rfl
@[simp] lemma op_map (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : (F.op).map f = F.map f := rfl

protected definition unop (F : Cᵒᵖ ⥤ Dᵒᵖ) : C ⥤ D :=
{ obj       := λ X, F.obj X,
  map       := λ X Y f, F.map f,
  map_id'   := F.map_id,
  map_comp' := by intros; apply F.map_comp }

@[simp] lemma unop_obj (F : Cᵒᵖ ⥤ Dᵒᵖ) (X : C) : (F.unop).obj X = F.obj X := rfl
@[simp] lemma unop_map (F : Cᵒᵖ ⥤ Dᵒᵖ) {X Y : C} (f : X ⟶ Y) : (F.unop).map f = F.map f := rfl

variables (C D)

definition op_hom : (C ⥤ D)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Dᵒᵖ) :=
{ obj := λ F, F.op,
  map := λ F G α,
  { app := λ X, α.app X,
    naturality' := λ X Y f, eq.symm (α.naturality f) } }

@[simp] lemma op_hom.obj (F : (C ⥤ D)ᵒᵖ) : (op_hom C D).obj F = F.op := rfl
@[simp] lemma op_hom.map_app {F G : (C ⥤ D)ᵒᵖ} (α : F ⟶ G) (X : C) :
  ((op_hom C D).map α).app X = α.app X := rfl

definition op_inv : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (C ⥤ D)ᵒᵖ :=
{ obj := λ F : Cᵒᵖ ⥤ Dᵒᵖ, F.unop,
  map := λ F G α,
  { app := λ X : C, α.app X,
    naturality' := λ X Y f, eq.symm (α.naturality f) } }

@[simp] lemma op_inv.obj (F : Cᵒᵖ ⥤ Dᵒᵖ) : (op_inv C D).obj F = F.unop := rfl
@[simp] lemma op_inv.map_app {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) (X : C) :
  ((op_inv C D).map α).app X = α.app X := rfl

-- TODO show these form an equivalence

instance {F : C ⥤ D} [full F] : full F.op :=
{ preimage := λ X Y f, F.preimage f }

instance {F : C ⥤ D} [faithful F] : faithful F.op :=
{ injectivity' := λ X Y f g h, by simpa using injectivity F h }

@[simp] lemma preimage_id (F : C ⥤ D) [fully_faithful F] (X : C) : F.preimage (𝟙 (F.obj X)) = 𝟙 X :=
injectivity F (by simp)

end

namespace category
variables {C} {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒟

@[simp] lemma op_id_app (F : (C ⥤ D)ᵒᵖ) (X : C) : (𝟙 F : F ⟹ F).app X = 𝟙 (F.obj X) := rfl
@[simp] lemma op_comp_app {F G H : (C ⥤ D)ᵒᵖ} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
  ((α ≫ β) : H ⟹ F).app X = (β : H ⟹ G).app X ≫ (α : G ⟹ F).app X := rfl
end category

section

variable (C)

/-- `functor.hom` is the hom-pairing, sending (X,Y) to X → Y, contravariant in X and covariant in Y. -/
definition hom : (Cᵒᵖ × C) ⥤ (Type v₁) :=
{ obj       := λ p, @category.hom C _ p.1 p.2,
  map       := λ X Y f, λ h, f.1 ≫ h ≫ f.2,
  map_id'   := by intros; ext; dsimp [category_theory.opposite]; simp,
  map_comp' := by intros; ext; dsimp [category_theory.opposite]; simp }

@[simp] lemma hom_obj (X : Cᵒᵖ × C) : (functor.hom C).obj X = @category.hom C _ X.1 X.2 := rfl
@[simp] lemma hom_pairing_map {X Y : Cᵒᵖ × C} (f : X ⟶ Y) :
  (functor.hom C).map f = λ h, f.1 ≫ h ≫ f.2 := rfl

end

end functor

end category_theory
