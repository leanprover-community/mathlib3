-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.category

namespace category_theory

universes v₁ u₁ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables (C : Type u₁) [𝒞 : category.{v₁} C]
include 𝒞

inductive zigzag' : bool → C → C → Type (max u₁ v₁)
| nil  : Π (X : C), zigzag' tt X X
| up   : Π {X Y Z : C} (z : zigzag' tt X Y) (f : Y ⟶ Z), zigzag' ff X Z
| down : Π {X Y Z : C} (z : zigzag' ff X Y) (f : Z ⟶ Y), zigzag' tt X Z

def zigzag := zigzag' C tt

variables {C}

open zigzag'

namespace zigzag

-- We represent a morphism of zigzags using an inductive type.
-- We don't impose the condition that maps between valleys are identities in the type signature,
-- but the constructors only produce morphisms satisfying this condition.
inductive hom' : Π {X Y Y' : C} {b : bool}, zigzag' C b X Y → zigzag' C b X Y' → (Y ⟶ Y') → Type (max u₁ v₁)
| nil : Π (X : C), hom' (nil X) (nil X) (𝟙 X)
| wedge  : Π {X Y Z : C} (α : Y ⟶ Z) {z : zigzag' C tt X Y} {z' : zigzag' C tt X Y} (f : hom' z z' (𝟙 Y)), hom' z ((z'.up α).down α) (𝟙 Y)
| bispan : Π {X Y Y' W Z : C} {π : Y ⟶ Y'} (α : W ⟶ Y) (β : W ⟶ Z) (γ : Z ⟶ Y') (h : α ≫ π = β ≫ γ) {z : zigzag' C ff X Y} {z' : zigzag' C ff X Y'} (f : hom' z z' π), hom' ((z.down α).up β) z' γ
| triangle_down : Π {X Y Y' Z : C} (π : Y ⟶ Y') (α : Z ⟶ Y) (β : Z ⟶ Y') (h : α ≫ π = β) {z : zigzag' C ff X Y} {z' : zigzag' C ff X Y'} (f : hom' z z' π), hom' (z.down α) (z'.down β) (𝟙 Z)
| triangle_up : Π {X Y Z Z' : C} (α : Y ⟶ Z) (β : Y ⟶ Z') (γ : Z ⟶ Z') (h : α ≫ γ = β) {z : zigzag' C tt X Y} {z' : zigzag' C tt X Y} (f : hom' z z' (𝟙 Y)), hom' (z.up α) (z'.up β) γ

open hom'

lemma ends_with_id : ∀ {X Y : C} (z z' : zigzag C X Y) (γ : Y ⟶ Y) (h : hom' z z' γ), γ = 𝟙 Y
| X Y z z' γ (nil _) := rfl
| X Y z z' γ (wedge _ _) := rfl
| X Y z z' γ (triangle_down _ _ _ _ _) := rfl

def hom {X Y : C} (z z' : zigzag C X Y) := hom' z z' (𝟙 Y)

set_option eqn_compiler.lemmas false -- :-(
def id' : Π {X Y : C} {b} (z : zigzag' C b X Y), hom' z z (𝟙 Y)
| X Y tt (nil _)    := nil X
| X Y ff (up z f)   := triangle_up   f f (𝟙 _) (by simp) (id' z)
| X Y tt (down z f) := triangle_down (𝟙 _) f f (by simp) (id' z)

def id {X Y : C} (z : zigzag C X Y) : hom z z := id' z

def comp' : Π {X Y Y' Y'' : C} {b} {z : zigzag' C b X Y} {z' : zigzag' C b X Y'} {z'' : zigzag' C b X Y''}
  {γ : Y ⟶ Y'} {γ' : Y' ⟶ Y''}
  (f : hom' z z' γ) (g : hom' z' z'' γ'), hom' z z'' (γ ≫ γ')
| X Y Y' Y'' b z z' z'' γ γ' (nil _) g := begin convert g, simp, end
| X Y Y' Y'' b z z' z'' γ γ' f (nil _) := begin convert f, simp, end

end zigzag

end category_theory
