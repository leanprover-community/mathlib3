/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.terminal

/-!
# Zero morphisms and zero objects

A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. (Notice this is extra
structure, not merely a property.)

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object.

## References
* https://en.wikipedia.org/wiki/Zero_morphism
-/

universes v u

open category_theory

namespace category_theory.limits

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

/-- A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. -/
class has_zero_morphisms :=
[has_zero : Π X Y : C, has_zero (X ⟶ Y)]
(comp_zero' : ∀ {X Y : C} (f : X ⟶ Y) (Z : C), f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) . obviously)
(zero_comp' : ∀ (X : C) {Y Z : C} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) . obviously)

attribute [instance] has_zero_morphisms.has_zero
restate_axiom has_zero_morphisms.comp_zero'
attribute [simp] has_zero_morphisms.comp_zero
restate_axiom has_zero_morphisms.zero_comp'
attribute [simp, reassoc] has_zero_morphisms.zero_comp

-- FIXME define is_initial and is_terminal, and define `has_zero_object` in terms of these

/-- A category "has a zero object" if it has an object which is both initial and terminal. -/
class has_zero_object :=
(zero : C)
(unique_to : Π X : C, unique (zero ⟶ X))
(unique_from : Π X : C, unique (X ⟶ zero))

variables [has_zero_object.{v} C]

variables {C}

/--
Construct a `has_zero C` for a category with a zero object.
This can not be a global instance as it will trigger for every `has_zero C` typeclass search.
-/
def zero_of_zero_object [has_zero_object.{v} C] : has_zero C :=
{ zero := has_zero_object.zero.{v} C }

local attribute [instance] zero_of_zero_object
local attribute [instance] has_zero_object.unique_to has_zero_object.unique_from

namespace has_zero_object

/-- A category with a zero object has zero morphisms. -/
def zero_morphisms_of_zero_object : has_zero_morphisms.{v} C :=
{ has_zero := λ X Y,
  { zero := inhabited.default (X ⟶ 0) ≫ inhabited.default (0 ⟶ Y) },
  zero_comp' := λ X Y Z f, by { dunfold has_zero.zero, rw category.assoc, congr, },
  comp_zero' := λ X Y Z f, by { dunfold has_zero.zero, rw ←category.assoc, congr, }}

/-- A zero object is in particular initial. -/
def has_initial_of_has_zero_object : has_initial.{v} C :=
has_initial_of_unique 0
/-- A zero object is in particular terminal. -/
def has_terminal_of_has_zero_object : has_terminal.{v} C :=
has_terminal_of_unique 0

end has_zero_object

end category_theory.limits
