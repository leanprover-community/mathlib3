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
@[reducible, to_additive AddGroup]
def Group : Type (u+1) := bundled group

namespace Group

@[to_additive add_group]
instance (G : Group) : group G := G.str

/-- Construct a bundled Group from the underlying type and typeclass. -/
@[to_additive] def of (X : Type u) [group X] : Group := bundled.of X

@[to_additive]
instance bundled_hom : bundled_hom _ :=
Mon.bundled_hom.induced_category @group.to_monoid

@[to_additive]
instance : has_one Group := ⟨Group.of punit⟩

@[to_additive has_forget_to_AddMon]
instance has_forget_to_Mon : has_forget₂ Group.{u} Mon.{u} :=
Mon.bundled_hom.induced_category_has_forget₂ _

end Group


/-- The category of commutative groups and group morphisms. -/
@[reducible, to_additive AddCommGroup]
def CommGroup : Type (u+1) := bundled comm_group

namespace CommGroup

@[to_additive add_comm_group]
instance (G : CommGroup) : comm_group G := G.str

/-- Construct a bundled CommGroup from the underlying type and typeclass. -/
@[to_additive] def of (G : Type u) [comm_group G] : CommGroup := bundled.of G

@[to_additive] instance : bundled_hom _ :=
Group.bundled_hom.induced_category @comm_group.to_group

@[to_additive has_forget_to_AddGroup]
instance has_forget_to_Group : has_forget₂ CommGroup.{u} Group.{u} :=
Group.bundled_hom.induced_category_has_forget₂ _

@[to_additive has_forget_to_AddCommMon]
instance has_forget_to_CommMon : has_forget₂ CommGroup.{u} CommMon.{u} :=
CommMon.bundled_hom.induced_category_has_forget₂ comm_group.to_comm_monoid

@[to_additive] instance : has_one CommGroup := ⟨CommGroup.of punit⟩

end CommGroup
