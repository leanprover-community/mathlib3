/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison
-/
import category_theory.products.basic

/-!
# Lemmas about functors out of product categories.
-/

open category_theory

namespace category_theory.bifunctor

universes v₁ v₂ v₃ u₁ u₂ u₃
variables {C : Type u₁} {D : Type u₂} {E : Type u₃}
variables [category.{v₁} C] [category.{v₂} D] [category.{v₃} E]

@[simp] lemma map_id (F : (C × D) ⥤ E) (X : C) (Y : D) :
  F.map ((𝟙 X, 𝟙 Y) : (X, Y) ⟶ (X, Y)) = 𝟙 (F.obj (X, Y)) :=
F.map_id (X, Y)

@[simp] lemma map_id_comp (F : (C × D) ⥤ E) (W : C) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map ((𝟙 W, f ≫ g) : (W, X) ⟶ (W, Z)) =
  F.map ((𝟙 W, f) : (W, X) ⟶ (W, Y)) ≫ F.map ((𝟙 W, g) : (W, Y) ⟶ (W, Z)) :=
by rw [←functor.map_comp,prod_comp,category.comp_id]

@[simp] lemma map_comp_id (F : (C × D) ⥤ E) (X Y Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map ((f ≫ g, 𝟙 W) : (X, W) ⟶ (Z, W)) =
  F.map ((f, 𝟙 W) : (X, W) ⟶ (Y, W)) ≫ F.map ((g, 𝟙 W) : (Y, W) ⟶ (Z, W)) :=
by rw [←functor.map_comp,prod_comp,category.comp_id]

@[simp] lemma diagonal (F : (C × D) ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
  F.map ((𝟙 X, g) : (X, Y) ⟶ (X, Y')) ≫ F.map ((f, 𝟙 Y') : (X, Y') ⟶ (X', Y')) =
  F.map ((f, g) : (X, Y) ⟶ (X', Y')) :=
by rw [←functor.map_comp, prod_comp, category.id_comp, category.comp_id]

@[simp] lemma diagonal' (F : (C × D) ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
  F.map ((f, 𝟙 Y) : (X, Y) ⟶ (X', Y)) ≫ F.map ((𝟙 X', g) : (X', Y) ⟶ (X', Y')) =
  F.map ((f, g) : (X, Y) ⟶ (X', Y')) :=
by rw [←functor.map_comp, prod_comp, category.id_comp, category.comp_id]

end category_theory.bifunctor
