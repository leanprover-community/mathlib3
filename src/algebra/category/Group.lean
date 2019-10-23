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

## Implementation notes

See the note [locally reducible category instances].
-/

universes u v

open category_theory

/-- The category of groups and group morphisms. -/
@[to_additive AddGroup]
def Group : Type (u+1) := induced_category Mon (bundled.map group.to_monoid)

namespace Group

/-- Construct a bundled Group from the underlying type and typeclass. -/
@[to_additive] def of (X : Type u) [group X] : Group := bundled.of X

local attribute [reducible] Group

@[to_additive]
instance : has_coe_to_sort Group := infer_instance

@[to_additive add_group]
instance (G : Group) : group G := G.str

@[to_additive]
instance : has_one Group := ⟨Group.of punit⟩

@[to_additive]
instance : concrete_category Group := infer_instance

@[to_additive has_forget_to_AddMon]
instance has_forget_to_Mon : has_forget₂ Group Mon := infer_instance

end Group


/-- The category of commutative groups and group morphisms. -/
@[to_additive AddCommGroup]
def CommGroup : Type (u+1) := induced_category Group (bundled.map comm_group.to_group)

namespace CommGroup

/-- Construct a bundled CommGroup from the underlying type and typeclass. -/
@[to_additive] def of (G : Type u) [comm_group G] : CommGroup := bundled.of G

local attribute [reducible] CommGroup

@[to_additive]
instance : has_coe_to_sort CommGroup := infer_instance

@[to_additive add_comm_group]
instance (G : CommGroup) : comm_group G := G.str

@[to_additive] instance : has_one CommGroup := ⟨CommGroup.of punit⟩

@[to_additive] instance : concrete_category CommGroup := infer_instance

@[to_additive has_forget_to_AddGroup]
instance has_forget_to_Group : has_forget₂ CommGroup Group := infer_instance

@[to_additive has_forget_to_AddCommMon]
instance has_forget_to_CommMon : has_forget₂ CommGroup CommMon :=
induced_category.has_forget₂ (λ G : CommGroup, CommMon.of G)

end CommGroup
