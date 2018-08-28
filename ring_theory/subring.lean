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
{ add_comm      := assume ⟨a,_⟩ ⟨b,_⟩, subtype.eq $ add_comm _ _,
  left_distrib  := assume ⟨a,_⟩ ⟨b,_⟩ ⟨c,_⟩, subtype.eq $ left_distrib _ _ _,
  right_distrib := assume ⟨a,_⟩ ⟨b,_⟩ ⟨c,_⟩, subtype.eq $ right_distrib _ _ _,
  .. subtype.add_group,
  .. subtype.monoid }

instance subtype.ring {S : set R} [is_subring S] : ring (subtype S) := subset.ring

namespace is_ring_hom

instance {S : set R} [is_subring S] : is_ring_hom (@subtype.val R S) :=
{ map_add := λ _ _, rfl,
  map_mul := λ _ _, rfl,
  map_one := rfl }

end is_ring_hom

variables {cR : Type u} [comm_ring cR]

instance subset.comm_ring {S : set cR} [is_subring S] : comm_ring S :=
{ mul_comm := λ ⟨a,_⟩ ⟨b,_⟩, subtype.eq $ mul_comm _ _,
  ..subset.ring
}

instance subtype.comm_ring {S : set cR} [is_subring S] : comm_ring (subtype S) := subset.comm_ring

variables [decidable_eq R]
 
noncomputable def polynomial.map {S : Type v} [comm_ring S] (f : S → cR) [is_ring_hom f] : polynomial S → polynomial cR :=
finsupp.map_range f (is_ring_hom.map_zero f)

def is_integral (S : set cR) [is_subring S] (r : cR) : Prop := 
∃ f : polynomial ↥S, (polynomial.monic f) ∧ polynomial.eval r (@polynomial.map cR _ ↥S _ (subtype.val) is_ring_hom.is_ring_hom f) = 0

def is_integrally_closed (S : set cR) [is_subring S] :=
∀ r : cR, (is_integral S r) → r ∈ S
