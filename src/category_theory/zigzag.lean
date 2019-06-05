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

open zigzag'

namespace zigzag

inductive hom : Π {X Y : C} {b : bool}, zigzag' C b X Y → zigzag' C b X Y → Type (max u₁ v₁)
| wedge : Π {X Y Z : C} (α : Y ⟶ Z) {z : zigzag' C tt X Y} {z' : zigzag' C tt X Y} (f : hom z z'), hom z ((z'.up α).down α)

end zigzag

end category_theory
