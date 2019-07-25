/-!
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

The category of types with binary relations as morphisms.
-/

import category_theory.category

namespace category_theory

universe u

/-- A type synonym for `Type`, which carries the category instance for which
    morphisms are binary relations. -/
def Rel := Type u

/-- The category of types with binary relations as morphisms. -/
-- We must work in `Type u` rather than `Sort u`, because
-- `X → Y → Prop` is in `Sort (max u 1)`.
def rel : large_category Rel.{u} :=
{ hom  := λ X Y, X → Y → Prop,
  id   := λ X, λ x y, x = y,
  comp := λ X Y Z f g x z, ∃ y, f x y ∧ g y z }

end category_theory
