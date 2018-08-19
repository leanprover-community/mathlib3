/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/

import algebra.group_power
import tactic.subtype_instance

namespace test_tactics

section
variables {α : Type*} [monoid α] {s : set α}
variables {β : Type*} [add_monoid β] {t : set β}

-- TODO(Simon) these could be generated from `monoid`
class is_submonoid (s : set α) : Prop :=
(one_mem : (1:α) ∈ s)
(mul_mem {a b} : a ∈ s → b ∈ s → a * b ∈ s)

instance subtype.monoid {s : set α} [is_submonoid s] : monoid s :=
by subtype_instance

class is_add_submonoid (s : set β) : Prop :=
(zero_mem : (0:β) ∈ s)
(add_mem {a b} : a ∈ s → b ∈ s → a + b ∈ s)

instance subtype.add_monoid {t : set β} [is_add_submonoid t] : add_monoid t :=
by subtype_instance
end

section
variables {α : Type*} [group α] {s : set α}
{β : Type*} [add_group β]

class is_subgroup (s : set α) extends is_submonoid s : Prop :=
(inv_mem {a} : a ∈ s → a⁻¹ ∈ s)

instance subtype.group {s : set α} [is_subgroup s] : group s :=
by subtype_instance

class is_add_subgroup (s : set β) extends is_add_submonoid s : Prop :=
(neg_mem {a} : a ∈ s → -a ∈ s)

instance subtype.add_group {s : set β} [is_add_subgroup s] : add_group s :=
by subtype_instance

end

section
variables {R : Type*} [ring R]


class is_subring  (S : set R) extends is_add_subgroup S, is_submonoid S : Prop.

instance subtype.ring {S : set R} [is_subring S] : ring S :=
by subtype_instance

variables {cR : Type*} [comm_ring cR]


instance subset.comm_ring {S : set cR} [is_subring S] : comm_ring S :=
by subtype_instance
end

section
variables {F : Type*} [field F] (s : set F)

class is_subfield extends is_subring s :=
(inv_mem : ∀ {x : F}, x ∈ s → x⁻¹ ∈ s)

instance subtype.field [is_subfield s] : field s :=
by subtype_instance
end

end test_tactics

