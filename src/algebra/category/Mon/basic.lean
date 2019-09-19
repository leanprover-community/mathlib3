/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import category_theory.concrete_category
import algebra.group

/-!
# Category instances for monoid, add_monoid, comm_monoid, and add_comm_monoid.

We introduce the bundled categories:
* `Mon`
* `AddMon`
* `CommMon`
* `AddCommMon`
along with the relevant forgetful functors between them.
-/

universes u v

open category_theory

/-- The category of monoids and monoid morphisms. -/
@[reducible, to_additive AddMon]
def Mon : Type (u+1) := bundled monoid

namespace Mon

/-- Construct a bundled Mon from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [monoid M] : Mon := bundled.of M

@[to_additive]
instance bundled_hom : bundled_hom @monoid_hom :=
⟨@monoid_hom.to_fun, @monoid_hom.id, @monoid_hom.comp, @monoid_hom.ext⟩

@[to_additive add_monoid]
instance (x : Mon) : monoid x := x.str

end Mon

/-- The category of commutative monoids and monoid morphisms. -/
@[reducible, to_additive AddCommMon]
def CommMon : Type (u+1) := bundled comm_monoid

namespace CommMon

/-- Construct a bundled CommMon from the underlying type and typeclass. -/
@[to_additive]
def of (X : Type u) [comm_monoid X] : CommMon := bundled.of X

@[to_additive]
instance bundled_hom : bundled_hom _ :=
Mon.bundled_hom.induced_category @comm_monoid.to_monoid

@[to_additive add_comm_monoid]
instance (x : CommMon) : comm_monoid x := x.str

@[to_additive has_forget_to_AddMon]
instance has_forget_to_Mon : has_forget₂ CommMon.{u} Mon.{u} :=
Mon.bundled_hom.full_subcategory_has_forget₂ _

end CommMon
