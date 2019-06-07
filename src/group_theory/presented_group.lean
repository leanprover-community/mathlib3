/-
Copyright (c) 2019 Michael Howes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Howes

Defining a group given by generators and relations
-/

import group_theory.free_group group_theory.quotient_group

variables {α : Type}

/-- Given a set of relations, rels, over a type α, presented_group constructs the group with
generators α and relations rels as a quotient of free_group α.-/
def presented_group (rels : set (list (α × bool))) : Type :=
    quotient_group.quotient $ group.normal_closure (set.image free_group.mk rels)

instance presented_group.group (rels : set (list (α × bool))) : group (presented_group (rels)) :=
quotient_group.group _

namespace to_group

/-
Presented groups satisfy a universal property. If β is a group and f : α → β is a map such that the
images of f satisfy all the given relations, thenf extends to a group homomorphism from
presented_group rels to β
-/

variables {β : Type} [group β] {f : α → β} {rels : set (list (α × bool))}

local notation `R` := set.image free_group.mk rels
local notation `F` := free_group.to_group f

lemma relations_in_kernel (h : ∀ r ∈ rels, free_group.to_group.aux f r = 1) : ∀ x ∈ R, F x = 1 :=
λ x ⟨r, w₁, w₂⟩, by {rw ←w₂, exact (h r w₁)}

lemma closure_subset_kernel (h : ∀ r ∈ rels, free_group.to_group.aux f r = 1) :
  group.normal_closure R ⊆ is_group_hom.ker F :=
group.normal_closure_subset (λ x w, (is_group_hom.mem_ker F).2 (relations_in_kernel h x w))

lemma closure_mapsto_zero (h : ∀ r ∈ rels, free_group.to_group.aux f r = 1) :
  ∀ x ∈ group.normal_closure R, F x = 1 :=
λ x w, (is_group_hom.mem_ker F).1  ((closure_subset_kernel h) w)

/-- The extension of a map f : α → β that satisfies the given relations to a group homomorphism
from presented_group rels → β. -/
def to_group (h : ∀ r ∈ rels, free_group.to_group.aux f r = 1) : (presented_group rels) → β :=
quotient_group.lift (group.normal_closure R) F (closure_mapsto_zero h)

instance to_group.is_group_hom (h : ∀ r ∈ rels, free_group.to_group.aux f r = 1) :
  is_group_hom (to_group h) :=
quotient_group.is_group_hom_quotient_lift _ _ _

end to_group
