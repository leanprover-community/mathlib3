-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import category_theory.embedding

namespace category_theory

universes u v

section
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

instance full_subcategory (Z : C → Prop) : category.{u v} {X : C // Z X} :=
{ hom  := λ X Y, X.1 ⟶ Y.1,
  id   := λ X, 𝟙 X.1,
  comp := λ _ _ _ f g, f ≫ g }

def full_subcategory_embedding (Z : C → Prop) : {X : C // Z X} ⥤ C :=
{ obj := λ X, X.1,
  map := λ _ _ f, f }

instance full_subcategory_full     (Z : C → Prop) : full     (full_subcategory_embedding Z) := by obviously
instance full_subcategory_faithful (Z : C → Prop) : faithful (full_subcategory_embedding Z) := by obviously
end

end category_theory