/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import group_theory.subgroup.basic
import group_theory.group_action.basic

/-!

# Fixing submonoid, fixing subgroup of an action

In the presence of of an action of a monoid or a group,
this file defines the fixing submonoid or the fixing subgroup,
and relates it to the set of fixed points via a Galois connection.

## Main definitions

* `fixing_submonoid M s` : in the presence of `mul_action M α` (with `monoid M`)
  it is the `submonoid M` consisting of elements which fix `s : set α` pointwise.

* `fixing_submonoid_fixed_points_gc M α` is the `galois_connection`
  that relates `fixing_submonoid` with `fixed_points`.

* `fixing_subgroup M s` : in the presence of `mul_action M α` (with `group M`)
  it is the `subgroup M` consisting of elements which fix `s : set α` pointwise.

* `fixing_subgroup_fixed_points_gc M α` is the `galois_connection`
  that relates `fixing_subgroup` with `fixed_points`.

TODO :

* Maybe other lemmas are useful

* Treat semigroups ?

-/

section monoid

open mul_action

variables (M : Type*) {α : Type*} [monoid M] [mul_action M α]

/-- The submonoid fixing a set under a `mul_action`. -/
@[to_additive /-" The additive submonoid fixing a set under an `add_action`. "-/]
def fixing_submonoid (s : set α) : submonoid M :=
{ carrier := { ϕ : M | ∀ x : s, ϕ • (x : α) = x },
  one_mem' := λ _, one_smul _ _,
  mul_mem' := λ x y hx hy z, by rw [mul_smul, hy z, hx z], }

lemma mem_fixing_submonoid_iff {s : set α} {m : M} :
  m ∈ fixing_submonoid M s ↔ ∀ y ∈ s, m • y = y :=
⟨λ hg y hy, hg ⟨y, hy⟩, λ h ⟨y, hy⟩, h y hy⟩

variable (α)

/-- The Galois connection between fixing submonoids and fixed points of a monoid action -/
theorem fixing_submonoid_fixed_points_gc : galois_connection
  (order_dual.to_dual ∘ (fixing_submonoid M))
  ((λ P : submonoid M, (fixed_points P α)) ∘ order_dual.of_dual) :=
λ s P, ⟨λ h s hs p, h p.2 ⟨s, hs⟩, λ h p hp s, h s.2 ⟨p, hp⟩⟩

lemma fixing_submonoid_antitone : antitone (λ (s : set α), fixing_submonoid M s) :=
(fixing_submonoid_fixed_points_gc M α).monotone_l

lemma fixed_points_antitone :
  antitone (λ (P : submonoid M), fixed_points P α) :=
(fixing_submonoid_fixed_points_gc M α).monotone_u.dual_left

/-- Fixing submonoid of union is intersection -/
lemma fixing_submonoid_union {s t : set α} :
  fixing_submonoid M (s ∪ t) = fixing_submonoid M s ⊓ fixing_submonoid M t :=
(fixing_submonoid_fixed_points_gc M α).l_sup

/-- Fixing submonoid of Union is intersection -/
lemma fixing_submonoid_Union {ι : Sort*} {s : ι → set α} :
  fixing_submonoid M (⋃ i, s i) = ⨅ i, fixing_submonoid M (s i) :=
(fixing_submonoid_fixed_points_gc M α).l_supr

/-- Fixed points of sup of submonoids is intersection -/
lemma fixed_points_submonoid_sup {P Q : submonoid M} :
  fixed_points ↥(P ⊔ Q) α = fixed_points P α ∩ fixed_points Q α :=
(fixing_submonoid_fixed_points_gc M α).u_inf

/-- Fixed points of supr of submonoids is intersection -/
lemma fixed_points_submonoid_supr {ι : Sort*} {P : ι → submonoid M} :
  fixed_points ↥(supr P) α = ⋂ i, fixed_points (P i) α :=
(fixing_submonoid_fixed_points_gc M α).u_infi

end monoid

section group

open mul_action

variables (M : Type*) {α : Type*} [group M] [mul_action M α]

/-- The subgroup fixing a set under a `mul_action`. -/
@[to_additive /-" The additive subgroup fixing a set under an `add_action`. "-/]
def fixing_subgroup (s : set α) : subgroup M :=
{ inv_mem' := λ _ hx z, by rw [inv_smul_eq_iff, hx z],
  ..fixing_submonoid M s, }

lemma mem_fixing_subgroup_iff {s : set α} {m : M} :
  m ∈ fixing_subgroup M s ↔ ∀ y ∈ s, m • y = y :=
⟨λ hg y hy, hg ⟨y, hy⟩, λ h ⟨y, hy⟩, h y hy⟩

variable (α)

/-- The Galois connection between fixing subgroups and fixed points of a group action -/
lemma fixing_subgroup_fixed_points_gc : galois_connection
  (order_dual.to_dual ∘ fixing_subgroup M)
  ((λ P : subgroup M, fixed_points P α) ∘ order_dual.of_dual) :=
λ s P, ⟨λ h s hs p, h p.2 ⟨s, hs⟩, λ h p hp s, h s.2 ⟨p, hp⟩⟩

lemma fixing_subgroup_antitone : antitone (fixing_subgroup M : set α → subgroup M) :=
(fixing_subgroup_fixed_points_gc M α).monotone_l

lemma fixed_points_subgroup_antitone :
  antitone (λ (P : subgroup M), fixed_points P α) :=
(fixing_subgroup_fixed_points_gc M α).monotone_u.dual_left

/-- Fixing subgroup of union is intersection -/
lemma fixing_subgroup_union {s t : set α} :
  fixing_subgroup M (s ∪ t) = fixing_subgroup M s ⊓ fixing_subgroup M t :=
(fixing_subgroup_fixed_points_gc M α).l_sup

/-- Fixing subgroup of Union is intersection -/
lemma fixing_subgroup_Union {ι : Sort*} {s : ι → set α} :
  fixing_subgroup M (⋃ i, s i) = ⨅ i, fixing_subgroup M (s i) :=
(fixing_subgroup_fixed_points_gc M α).l_supr

/-- Fixed points of sup of subgroups is intersection -/
lemma fixed_points_subgroup_sup {P Q : subgroup M} :
  fixed_points ↥(P ⊔ Q) α = fixed_points P α ∩ fixed_points Q α :=
(fixing_subgroup_fixed_points_gc M α).u_inf

/-- Fixed points of supr of subgroups is intersection -/
lemma fixed_points_subgroup_supr {ι : Sort*} {P : ι → subgroup M} :
  fixed_points ↥(supr P) α = ⋂ i, fixed_points (P i) α :=
(fixing_subgroup_fixed_points_gc M α).u_infi

end group
