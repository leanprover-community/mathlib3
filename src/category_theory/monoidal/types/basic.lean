/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import category_theory.monoidal.functor
import category_theory.monoidal.of_chosen_finite_products.basic
import category_theory.limits.shapes.types
import logic.equiv.fin

/-!
# The category of types is a monoidal category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open category_theory
open category_theory.limits
open tactic

universes v u

namespace category_theory

instance types_monoidal : monoidal_category.{u} (Type u) :=
monoidal_of_chosen_finite_products (types.terminal_limit_cone) (types.binary_product_limit_cone)

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

/-- If `F` is a monoidal functor out of `Type`, it takes the (n+1)st cartesian power
of a type to the image of that type, tensored with the image of the nth cartesian power. -/
-- We don't yet have an API for tensor products indexed by finite ordered types,
-- but it would be nice to state how monoidal functors preserve these.
noncomputable
def monoidal_functor.map_pi {C : Type*} [category C] [monoidal_category C]
  (F : monoidal_functor Type* C) (n : ℕ) (β : Type*) :
  F.obj (fin (n+1) → β) ≅ F.obj β ⊗ F.obj (fin n → β) :=
functor.map_iso _ (equiv.pi_fin_succ n β).to_iso ≪≫ (as_iso (F.μ β (fin n → β))).symm

end category_theory
