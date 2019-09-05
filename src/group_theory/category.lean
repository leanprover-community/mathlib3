/- Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Introduce Group -- the category of groups.

Currently only the basic setup.
Copied from monoids.lean.
-/

import algebra.punit_instances
import algebra.Mon.basic

universes u v

open category_theory

/-- The category of groups and group morphisms. -/
@[reducible, to_additive AddGroup]
def Group : Type (u+1) := bundled group

namespace Group

@[to_additive add_group]
instance (G : Group) : group G := G.str

@[to_additive] def of (X : Type u) [group X] : Group := bundled.of X

@[to_additive]
instance bundled_hom : bundled_hom _ :=
Mon.bundled_hom.full_subcategory @group.to_monoid

@[to_additive]
instance : has_one Group := ⟨Group.of punit⟩

end Group


/-- The category of commutative groups and group morphisms. -/
@[reducible, to_additive AddCommGroup]
def CommGroup : Type (u+1) := bundled comm_group

namespace CommGroup

@[to_additive add_comm_group]
instance (G : CommGroup) : comm_group G := G.str

@[to_additive] def of (G : Type u) [comm_group G] : CommGroup := bundled.of G

@[to_additive] instance : bundled_hom _ :=
Group.bundled_hom.full_subcategory @comm_group.to_group

@[to_additive has_forget_to_AddGroup]
instance has_forget_to_Group : has_forget CommGroup.{u} Group.{u} :=
Group.bundled_hom.full_subcategory_has_forget _

@[to_additive] instance : has_one CommGroup := ⟨CommGroup.of punit⟩

end CommGroup
