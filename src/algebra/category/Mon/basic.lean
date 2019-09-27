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
@[to_additive AddMon]
def Mon : Type (u+1) := bundled monoid

namespace Mon

/-- Construct a bundled Mon from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [monoid M] : Mon := bundled.of M

local attribute [reducible] Mon

@[to_additive]
instance : has_coe_to_sort Mon := infer_instance

@[to_additive add_monoid]
instance (M : Mon) : monoid M := M.str

@[to_additive]
instance bundled_hom : bundled_hom @monoid_hom :=
⟨@monoid_hom.to_fun, @monoid_hom.id, @monoid_hom.comp, @monoid_hom.coe_inj⟩

@[to_additive]
instance : concrete_category Mon := infer_instance

end Mon

/-- The category of commutative monoids and monoid morphisms. -/
@[to_additive AddCommMon]
def CommMon : Type (u+1) := induced_category Mon (bundled.map @comm_monoid.to_monoid)

namespace CommMon

/-- Construct a bundled CommMon from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [comm_monoid M] : CommMon := bundled.of M

local attribute [reducible] CommMon

@[to_additive]
instance : has_coe_to_sort Mon := infer_instance

@[to_additive add_comm_monoid]
instance (M : CommMon) : comm_monoid M := M.str

@[to_additive]
instance : concrete_category CommMon := infer_instance

@[to_additive has_forget_to_AddMon]
instance has_forget_to_Mon : has_forget₂ CommMon Mon := infer_instance

end CommMon
