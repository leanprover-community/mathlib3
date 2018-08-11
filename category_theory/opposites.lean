-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.functor
import category_theory.products
import category_theory.types

namespace category_theory

universes u₁ v₁ u₂ v₂

def op (C : Type u₁) : Type u₁ := C

notation C `ᵒᵖ` := op C

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞

instance opposite : category.{u₁ v₁} (Cᵒᵖ) := 
{ Hom     := λ X Y : C, Y ⟶ X,
  comp    := λ _ _ _ f g, g ≫ f,
  id      := λ X, 𝟙 X,
  id_comp := begin /- `obviously'` says: -/ intros, simp end,
  comp_id := begin /- `obviously'` says: -/ intros, simp end,
  assoc   := begin /- `obviously'` says: -/ intros, simp end }

namespace functor

variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒟

definition opposite (F : C ↝ D) : (Cᵒᵖ) ↝ (Dᵒᵖ) := 
{ obj      := λ X, F X,
  map      := λ X Y f, F.map f,
  map_id   := begin /- `obviously'` says: -/ intros, erw [map_id], refl, end,
  map_comp := begin /- `obviously'` says: -/ intros, erw [map_comp], refl end }

@[simp] lemma opposite_obj (F : C ↝ D) (X : C) : (F.opposite) X = F X := rfl
@[simp] lemma opposite_map (F : C ↝ D) {X Y : C} (f : X ⟶ Y) : (F.opposite).map f = F.map f := rfl
                   
end functor

variable (C)

definition hom_pairing : (Cᵒᵖ × C) ↝ (Type v₁) := 
{ obj      := λ p, @category.Hom C _ p.1 p.2,
  map      := λ X Y f, λ h, f.1 ≫ h ≫ f.2,
  map_id   := begin /- `obviously'` says: -/ intros, apply funext, intros, cases X, dsimp at *, simp, erw [category.id_comp_lemma] end,
  map_comp := begin /- `obviously'` says: -/ intros, apply funext, intros, cases f, cases g, cases X, cases Y, cases Z, dsimp at *, simp, erw [category.assoc] end }

@[simp] lemma hom_pairing_obj (X : Cᵒᵖ × C) : (hom_pairing C) X = @category.Hom C _ X.1 X.2 := rfl
@[simp] lemma hom_pairing_map {X Y : Cᵒᵖ × C} (f : X ⟶ Y) : (hom_pairing C).map f = λ h, f.1 ≫ h ≫ f.2 := rfl

end category_theory