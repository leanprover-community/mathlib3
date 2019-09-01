/- Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

Introduce Mon -- the category of monoids.

Currently only the basic setup.
-/

import category_theory.concrete_category
import category_theory.bundled_hom
import algebra.group.hom

universes u v

open category_theory

/-- The category of monoids and monoid morphisms. -/
@[reducible] def Mon : Type (u+1) := bundled monoid

/-- The category of commutative monoids and monoid morphisms. -/
@[reducible] def CommMon : Type (u+1) := bundled comm_monoid

namespace Mon

instance (x : Mon) : monoid x := x.str

-- TODO a tactic, so we could write `by bundled_hom monoid_hom`?
instance : bundled_hom.{u} monoid :=
{ hom := λ X Y _ _, by exactI X →* Y,
  to_fun := λ X Y _ _ f, by exactI f.to_fun,
  id := λ X _, by exactI monoid_hom.id X,
  comp := λ X Y Z _ _ _ f g, by exactI monoid_hom.comp g f }

/-- Construct a bundled monoid from an unbundled monoid. -/
def of (X : Type u) [monoid X] : Mon := ⟨X⟩

/-- The forgetful functor from monoids to underlying types. -/
abbreviation forget : Mon.{u} ⥤ Type u := bundled_hom.forget

-- We already know that all forgetful functors out of bundled hom categories are faithful:
example : faithful forget := by apply_instance

end Mon

namespace CommMon

instance (x : CommMon) : comm_monoid x := x.str

instance : bundled_hom.{u} comm_monoid :=
{ hom := λ X Y _ _, by exactI X →* Y,
  to_fun := λ X Y _ _ f, by exactI f.to_fun,
  id := λ X _, by exactI monoid_hom.id X,
  comp := λ X Y Z _ _ _ f g, by exactI monoid_hom.comp g f }

/-- Construct a bundled commutative monoid from an unbundled commutative monoid. -/
def of (X : Type u) [comm_monoid X] : CommMon := ⟨X⟩

/-- The forgetful functor from commutative monoids to underlying types. -/
abbreviation forget : CommMon.{u} ⥤ Type u := bundled_hom.forget

/-- The forgetful functor from commutative monoids to monoids. -/
def forget_to_Mon : CommMon ⥤ Mon := bundled_hom.forget_to comm_monoid monoid

instance : faithful (forget_to_Mon) := {}
instance : full (forget_to_Mon) :=
{ preimage := λ X Y f, f }

end CommMon
