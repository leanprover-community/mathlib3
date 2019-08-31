/- Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

Introduce Mon -- the category of monoids.

Currently only the basic setup.
-/

import category_theory.concrete_category algebra.group.hom

universes u v

open category_theory

/-- The category of monoids and monoid morphisms. -/
@[reducible] def Mon : Type (u+1) := bundled monoid

/-- The category of commutative monoids and monoid morphisms. -/
@[reducible] def CommMon : Type (u+1) := bundled comm_monoid

namespace Mon

instance (x : Mon) : monoid x := x.str

-- TODO provide a generic constructor
instance category_Mon : large_category Mon.{u} :=
{ hom := λ X Y, X →* Y,
  id := λ X, monoid_hom.id X,
  comp := λ X Y Z f g, @monoid_hom.comp X.α Y.α Z.α _ _ _ g f, }

def of (X : Type u) [monoid X] : Mon := ⟨X⟩

def forget : Mon ⥤ Type u :=
{ obj := λ X, X.α,
  map := λ X Y f, monoid_hom.to_fun f }

-- TODO remove?
instance hom_is_monoid_hom {R S : Mon} (f : R ⟶ S) : is_monoid_hom (f : R → S) := by apply_instance

-- TODO remove
-- /-- Morphisms in `Mon` are defined using `subtype is_monoid_hom`,
-- so we provide a canonical bijection with `R →* S`. -/
-- def hom_equiv_monoid_hom (R S : Mon) : (R ⟶ S) ≃ (R →* S) :=
-- { to_fun := λ f, @as_monoid_hom _ _ _ _ f.val f.property,
--   inv_fun := λ f, ⟨f, f.is_monoid_hom⟩,
--   right_inv := λ f, by rcases f; refl,
--   left_inv := λ f, by rcases f; refl }

end Mon

namespace CommMon

instance (x : CommMon) : comm_monoid x := x.str

instance category_CommMon : large_category CommMon.{u} :=
{ hom := λ X Y, X →* Y,
  id := λ X, monoid_hom.id X,
  comp := λ X Y Z f g, @monoid_hom.comp X.α Y.α Z.α _ _ _ g f, }

def of (X : Type u) [comm_monoid X] : CommMon := ⟨X⟩

abbreviation forget : CommMon.{u} ⥤ Type u :=
{ obj := λ X, X.α,
  map := λ X Y f, monoid_hom.to_fun f }

-- TODO provide a generic constructor
/-- The forgetful functor from commutative monoids to monoids. -/
def forget_to_Mon : CommMon ⥤ Mon :=
{ obj := λ X, Mon.of X.α,
  map := λ X Y f, f }

instance : faithful (forget_to_Mon) := {}

end CommMon
