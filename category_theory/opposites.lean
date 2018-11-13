-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.products
import category_theory.types

namespace category_theory

universes u₁ v₁ u₂ v₂

def op (C : Type u₁) : Type u₁ := C

notation C `ᵒᵖ`:80 := op C

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞

instance opposite : category.{u₁ v₁} (Cᵒᵖ) :=
{ hom  := λ X Y : C, Y ⟶ X,
  comp := λ _ _ _ f g, g ≫ f,
  id   := λ X, 𝟙 X }

def op_op : (Cᵒᵖ)ᵒᵖ ⥤ C :=
{ obj := λ X, X,
  map := λ X Y f, f }

-- TODO this is an equivalence

namespace functor

variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒟

variables (C D)

definition op_hom : (C ⥤ D)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Dᵒᵖ) :=
{ obj := λ F : C ⥤ D,
  { obj       := λ X, F.obj X,
    map       := λ X Y f, F.map f,
    map_id'   := begin /- `obviously'` says: -/ intros, erw [map_id], refl, end,
    map_comp' := begin /- `obviously'` says: -/ intros, erw [map_comp], refl end },
  map := λ F G α,
  { app := λ X, α.app X,
    naturality' := λ X Y f, eq.symm (α.naturality f) } }

namespace op_hom
@[simp] lemma map_app {F G : (C ⥤ D)ᵒᵖ} (α : F ⟶ G) (X : C) : ((op_hom C D).map α).app X = α.app X := rfl
end op_hom

definition op_inv : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (C ⥤ D)ᵒᵖ :=
{ obj := λ F : Cᵒᵖ ⥤ Dᵒᵖ,
  { obj       := λ X, F.obj X,
    map       := λ X Y f, F.map f,
    map_id'   := begin /- `obviously'` says: -/ intros, erw [map_id], refl, end,
    map_comp' := begin /- `obviously'` says: -/ intros, erw [map_comp], refl end },
  map := λ F G α,
  { app := λ X : C, α.app X,
    naturality' := λ X Y f, eq.symm (α.naturality f) } }

namespace op_inv
@[simp] lemma map_app {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) (X : C) : ((op_inv C D).map α).app X = α.app X := rfl
end op_inv

-- TODO show these form an equivalence

variables {C D}

protected definition op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ := (@op_hom C _ D _).obj (F : (C ⥤ D)ᵒᵖ)

@[simp] lemma opposite_obj (F : C ⥤ D) (X : C) : (F.op).obj X = F.obj X := rfl
@[simp] lemma opposite_map (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : (F.op).map f = F.map f := rfl

end functor

namespace functor
variable (C)

/-- `functor.hom` is the hom-pairing, sending (X,Y) to X → Y, contravariant in X and covariant in Y. -/
definition hom : (Cᵒᵖ × C) ⥤ (Type v₁) :=
{ obj       := λ p, @category.hom C _ p.1 p.2,
  map       := λ X Y f, λ h, f.1 ≫ h ≫ f.2,
  map_id'   := begin /- `obviously'` says: -/ intros, ext, intros, cases X, dsimp at *, simp, erw [category.id_comp] end,
  map_comp' := begin /- `obviously'` says: -/ intros, ext, intros, cases f, cases g, cases X, cases Y, cases Z, dsimp at *, simp, erw [category.assoc] end }

@[simp] lemma hom_obj (X : Cᵒᵖ × C) : (functor.hom C).obj X = @category.hom C _ X.1 X.2 := rfl
@[simp] lemma hom_pairing_map {X Y : Cᵒᵖ × C} (f : X ⟶ Y) : (functor.hom C).map f = λ h, f.1 ≫ h ≫ f.2 := rfl

end functor

end category_theory