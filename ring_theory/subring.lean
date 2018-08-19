/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import group_theory.subgroup
import data.polynomial
import algebra.ring

local attribute [instance] classical.prop_decidable
universes u v

open group

variables {R : Type u} [ring R]

/-- `S` is a subring: a set containing 1 and closed under multiplication, addition and and additive inverse. -/
class is_subring  (S : set R) extends is_add_subgroup S, is_submonoid S : Prop.

instance subset.ring {S : set R} [is_subring S] : ring S :=
by subtype_instance

instance subtype.ring {S : set R} [is_subring S] : ring (subtype S) := subset.ring

namespace is_ring_hom

instance {S : set R} [is_subring S] : is_ring_hom (@subtype.val R S) :=
by refine {..} ; intros ; refl

end is_ring_hom

variables {cR : Type u} [comm_ring cR]

instance subset.comm_ring {S : set cR} [is_subring S] : comm_ring S :=
by subtype_instance

instance subtype.comm_ring {S : set cR} [is_subring S] : comm_ring (subtype S) := subset.comm_ring