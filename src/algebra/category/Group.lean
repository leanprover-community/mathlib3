/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import algebra.punit_instances
import algebra.category.Mon.basic

/-!
# Category instances for group, add_group, comm_group, and add_comm_group.

We introduce the bundled categories:
* `Group`
* `AddGroup`
* `CommGroup`
* `AddCommGroup`
along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/

universes u v

open category_theory

/-- The category of groups and group morphisms. -/
@[to_additive AddGroup]
def Group : Type (u+1) := induced_category Mon (bundled.map group.to_monoid.{u})

namespace Group
local attribute [reducible] Group

-- Setup instances while `Group` is reducible:
@[to_additive] instance : concrete_category Group.{u} := infer_instance
@[to_additive] instance : has_forget₂ Group.{u} Mon.{u} := infer_instance
@[to_additive] instance (G : Group) : group G := G.str
@[to_additive] instance : has_coe_to_sort Group.{u} := infer_instance
@[to_additive] instance (G H : Group.{u}) : has_coe_to_fun (G ⟶ H) := concrete_category.has_coe_to_fun

/-- Construct a bundled Group from the underlying type and typeclass. -/
@[to_additive] def of (G : Type u) [group G] : Group := bundled.of G

@[to_additive] instance : has_one Group := ⟨Group.of punit⟩

end Group

/-- The category of commutative groups and group morphisms. -/
@[to_additive AddCommGroup]
def CommGroup : Type (u+1) := induced_category Group (bundled.map comm_group.to_group.{u})

namespace CommGroup
local attribute [reducible] CommGroup

-- Setup instances while `CommGroup` is reducible:
@[to_additive] instance : concrete_category CommGroup.{u} := infer_instance
@[to_additive] instance : has_forget₂ CommGroup.{u} Group.{u} := infer_instance
@[to_additive] instance (G : CommGroup) : comm_group G := G.str
@[to_additive] instance : has_coe_to_sort CommGroup.{u} := infer_instance
@[to_additive] instance (G H : CommGroup.{u}) : has_coe_to_fun (G ⟶ H) := concrete_category.has_coe_to_fun

/-- Construct a bundled CommGroup from the underlying type and typeclass. -/
@[to_additive] def of (G : Type u) [comm_group G] : CommGroup := bundled.of G

@[to_additive has_forget_to_AddCommMon]
instance has_forget_to_CommMon : has_forget₂ CommGroup.{u} CommMon.{u} :=
induced_category.has_forget₂ (λ G : CommGroup, CommMon.of G)

@[to_additive] instance : has_one CommGroup := ⟨CommGroup.of punit⟩

end CommGroup
