/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import category_theory.monoidal.of_has_finite_products
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.types

open category_theory
open category_theory.limits
open tactic

universes u

namespace category_theory.monoidal

local attribute [instance] types.types_has_terminal types.types_has_binary_products
local attribute [instance] monoidal_of_has_finite_products symmetric_of_has_finite_products

instance types_monoidal : monoidal_category.{u} (Type u) := by apply_instance
instance types_symmetric : symmetric_category.{u} (Type u) := by apply_instance

@[simp] lemma tensor_apply {W X Y Z : Type u} (f : W ⟶ X) (g : Y ⟶ Z) (p : W ⊗ Y) :
  (f ⊗ g) p = (f p.1, g p.2) := rfl

@[simp] lemma left_unitor_hom_apply {X : Type u} {x : X} {p : punit} :
  ((λ_ X).hom : (𝟙_ (Type u)) ⊗ X → X) (p, x) = x := rfl
@[simp] lemma left_unitor_inv_apply {X : Type u} {x : X} :
  ((λ_ X).inv : X ⟶ (𝟙_ (Type u)) ⊗ X) x = (punit.star, x) := rfl

@[simp] lemma right_unitor_hom_apply {X : Type u} {x : X} {p : punit} :
  ((ρ_ X).hom : X ⊗ (𝟙_ (Type u)) → X) (x, p) = x := rfl
@[simp] lemma right_unitor_inv_apply {X : Type u} {x : X} :
  ((ρ_ X).inv : X ⟶ X ⊗ (𝟙_ (Type u))) x = (x, punit.star) := rfl

@[simp] lemma associator_hom_apply {X Y Z : Type u} {x : X} {y : Y} {z : Z} :
  ((α_ X Y Z).hom : (X ⊗ Y) ⊗ Z → X ⊗ (Y ⊗ Z)) ((x, y), z) = (x, (y, z)) := rfl
@[simp] lemma associator_inv_apply {X Y Z : Type u} {x : X} {y : Y} {z : Z} :
  ((α_ X Y Z).inv : X ⊗ (Y ⊗ Z) → (X ⊗ Y) ⊗ Z) (x, (y, z)) = ((x, y), z) := rfl

end category_theory.monoidal
