/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import order.bounded_lattice
import category_theory.punit
import category_theory.limits.shapes.terminal

/-!
# Category structures on `option C`, `with_bot C`, and `with_top C`, along with basic constructions.

## Categories

We define

* a category structure on `option C`, so there are no morphisms to or from `none`,
  and the morphisms `some X ⟶ some Y` are just the original morphisms `X ⟶ Y`.

* a category structure on `with_bot C`, so `none` has a unique morphism to every object,
  and the morphisms `some X ⟶ some Y` are just the original morphisms `X ⟶ Y`.

* a category structure on `with_top C`, so `none` has a unique morphism from every object,
  and the morphisms `some X ⟶ some Y` are just the original morphisms `X ⟶ Y`.

## Limits

By construction, `with_bot C` has an initial object, and `with_top C` has a terminal object.
-/

universes v₁ u₁

open category_theory.limits

namespace category_theory

variables (C : Type u₁) [𝒞 : category.{v₁} C]
include 𝒞

section
local attribute [tidy] tactic.case_bash

instance category_option : category.{v₁} (option C) :=
{ hom := λ X Y, match X, Y with
  | some X, some Y := X ⟶ Y
  | none, none := punit
  | _, _ := pempty
  end,
  id := λ X, match X with
  | some X := 𝟙 X
  | none := punit.star
  end,
  comp := λ X Y Z f g, match X, Y, Z, f, g with
  | some X, some Y, some Z, f, g := f ≫ g
  | none, none, none, _, _ := punit.star
  end }

instance category_with_bot : category.{v₁} (with_bot C) :=
{ hom := λ X Y, match X, Y with
  | some X, some Y := X ⟶ Y
  | none, _ := punit
  | _, _ := pempty
  end,
  id := λ X, match X with
  | some X := 𝟙 X
  | none := punit.star
  end,
  comp := λ X Y Z f g, match X, Y, Z, f, g with
  | some X, some Y, some Z, f, g := f ≫ g
  | none, _, _, _, _ := punit.star
  end }

instance category_with_top : category.{v₁} (with_top C) :=
{ hom := λ X Y, match X, Y with
  | some X, some Y := X ⟶ Y
  | some X, none := punit
  | none, some Y := pempty
  | none, none := punit
  end,
  id := λ X, match X with
  | some X := 𝟙 X
  | none := punit.star
  end,
  comp := λ X Y Z f g, match X, Y, Z, f, g with
  | some X, some Y, some Z, f, g := f ≫ g
  | some X, some Y, none, _, _ := punit.star
  | some X, none, none, _, _ := punit.star
  | none, none, none, _, _ := punit.star
  end }
end

namespace functor

def none : punit.{u₁+1} ⥤ option C :=
{ obj := λ X, none,
  map := λ X Y f, 𝟙 _ }

instance full_none : full (none C) :=
{ preimage := λ X Y f, by { cases X, cases Y, exact punit.star } }
instance faithful_none : faithful (none C) := {}

def some : C ⥤ option C :=
{ obj := λ X, some X,
  map := λ X Y f, f }

instance full_some : full (some C) :=
{ preimage := λ X Y f, f }
instance faithful_some : faithful (some C) := {}

section
local attribute [tidy] tactic.case_bash

def option_to_with_bot : option C ⥤ with_bot C :=
{ obj := λ X, X,
  map := λ X Y f, match X, Y, f with
  | option.some X, option.some Y, f := f
  | option.none, option.none, f := punit.star
  end }

instance faithful_option_to_with_bot : faithful (option_to_with_bot C) := {}

def option_to_with_top : option C ⥤ with_top C :=
{ obj := λ X, X,
  map := λ X Y f, match X, Y, f with
  | option.some X, option.some Y, f := f
  | option.none, option.none, f := punit.star
  end }

instance faithful_option_to_with_top : faithful (option_to_with_top C) := {}

end

end functor

end category_theory


namespace category_theory

variables (C : Type u₁) [𝒞 : category.{v₁+1} C]
include 𝒞

instance has_initial_with_bot : has_initial.{v₁} (with_bot C) :=
has_initial.of_unique none (λ X, by tidy)

local attribute [tidy] tactic.case_bash

instance has_terminal_with_bot : has_terminal.{v₁} (with_top C) :=
has_terminal.of_unique none (λ X, by tidy)

end category_theory

-- TODO prove the equivalence between `option C` and `C ⊕ punit`.
