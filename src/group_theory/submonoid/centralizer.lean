/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import group_theory.subsemigroup.centralizer
import group_theory.submonoid.center

/-!
# Centralizers of magmas and monoids

## Main definitions

* `submonoid.centralizer`: the centralizer of a subset of a monoid
* `add_submonoid.centralizer`: the centralizer of a subset of an additive monoid

We provide `subgroup.centralizer`, `add_subgroup.centralizer` in other files.
-/

variables {M : Type*} {S T : set M}

namespace submonoid
section
variables [monoid M] (S)

/-- The centralizer of a subset of a monoid `M`. -/
@[to_additive "The centralizer of a subset of an additive monoid."]
def centralizer : submonoid M :=
{ carrier := S.centralizer,
  one_mem' := S.one_mem_centralizer,
  mul_mem' := λ a b, set.mul_mem_centralizer }

@[simp, norm_cast, to_additive] lemma coe_centralizer : ↑(centralizer S) = S.centralizer := rfl

lemma centralizer_to_subsemigroup : (centralizer S).to_subsemigroup = subsemigroup.centralizer S :=
rfl

lemma _root_.add_submonoid.centralizer_to_add_subsemigroup {M} [add_monoid M] (S : set M) :
  (add_submonoid.centralizer S).to_add_subsemigroup = add_subsemigroup.centralizer S :=
rfl

attribute [to_additive add_submonoid.centralizer_to_add_subsemigroup]
  submonoid.centralizer_to_subsemigroup

variables {S}

@[to_additive] lemma mem_centralizer_iff {z : M} : z ∈ centralizer S ↔ ∀ g ∈ S, g * z = z * g :=
iff.rfl

@[to_additive] instance decidable_mem_centralizer [decidable_eq M] [fintype M]
  [decidable_pred (∈ S)] : decidable_pred (∈ centralizer S) :=
λ _, decidable_of_iff' _ mem_centralizer_iff

@[to_additive]
lemma centralizer_le (h : S ⊆ T) : centralizer T ≤ centralizer S :=
set.centralizer_subset h

variables (M)

@[simp, to_additive]
lemma centralizer_univ : centralizer set.univ = center M :=
set_like.ext' (set.centralizer_univ M)

end

end submonoid
