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
@[reducible, to_additive AddMon]
def Mon : Type (u+1) := bundled monoid

namespace Mon

@[to_additive add_monoid]
instance (x : Mon) : monoid x := x.str

@[to_additive]
def of (M : Type u) [monoid M] : Mon := bundled.of M

@[to_additive]
instance bundled_hom : bundled_hom @monoid_hom :=
⟨@monoid_hom.to_fun, @monoid_hom.ext, @monoid_hom.id, by intros; refl,
 @monoid_hom.comp, by intros; refl⟩

end Mon

/-- The category of commutative monoids and monoid morphisms. -/
@[reducible, to_additive AddCommMon]
def CommMon : Type (u+1) := bundled comm_monoid

namespace CommMon

@[to_additive add_comm_monoid]
instance (x : CommMon) : comm_monoid x := x.str

@[to_additive]
def of (X : Type u) [comm_monoid X] : CommMon := bundled.of X

@[to_additive]
instance bundled_hom : bundled_hom _ :=
Mon.bundled_hom.restrict_str @comm_monoid.to_monoid

@[to_additive has_forget_to_AddMon]
instance has_forget_to_Mon : has_forget CommMon.{u} Mon.{u} :=
by apply bundled_hom.restrict_str_has_forget

end CommMon
