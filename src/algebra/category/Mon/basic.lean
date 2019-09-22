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
local attribute [reducible] Mon

@[to_additive]
instance bundled_hom : bundled_hom @monoid_hom :=
⟨@monoid_hom.to_fun, @monoid_hom.id, @monoid_hom.comp, @monoid_hom.ext⟩

-- Setup instances while `Group` is reducible:
@[to_additive] instance : concrete_category Mon.{u} := infer_instance
@[to_additive] instance (M : Mon) : monoid M := M.str
@[to_additive] instance : has_coe_to_sort Mon.{u} := infer_instance
@[to_additive] instance (X Y : Mon.{u}) : has_coe_to_fun (X ⟶ Y) := concrete_category.has_coe_to_fun

/-- Construct a bundled Mon from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [monoid M] : Mon := bundled.of M

end Mon

/-- The category of commutative monoids and monoid morphisms. -/
@[to_additive AddCommMon]
def CommMon : Type (u+1) := induced_category Mon (bundled.map comm_monoid.to_monoid.{u})

namespace CommMon
local attribute [reducible] CommMon

-- Setup instances while `CommMon` is reducible:
@[to_additive] instance : concrete_category CommMon.{u} := infer_instance
@[to_additive] instance : has_forget₂ CommMon.{u} Mon.{u} := infer_instance
@[to_additive] instance (M : CommMon) : comm_monoid M := M.str
@[to_additive] instance : has_coe_to_sort CommMon.{u} := infer_instance
@[to_additive] instance (M N : CommMon.{u}) : has_coe_to_fun (M ⟶ N) := concrete_category.has_coe_to_fun

/-- Construct a bundled CommMon from the underlying type and typeclass. -/
@[to_additive]
def of (X : Type u) [comm_monoid X] : CommMon := bundled.of X

end CommMon
