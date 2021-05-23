/-
Copyright (c) 2019 Michael Howes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Howes
-/
import group_theory.free_group
import group_theory.quotient_group

/-!
# Defining a group given by generators and relations

Given a subset `rels` of relations of the free group on a type `α`, this file constructs the group
given by generators `x : α` and relations `r ∈ rels`.

## Main definitions

* `presented_group rels`: the quotient group of the free group on a type `α` by a subset `rels` of
  relations of the free group on `α`.
* `of`: The canonical map from `α` to a presented group with generators `α`.
* `to_group f`: the canonical group homomorphism `presented_group rels → G`, given a function
  `f : α → G` from a type `α` to a group `G` which satisfies the relations `rels`.

## Tags

generators, relations, group presentations
-/

variables {α : Type}

/-- Given a set of relations, rels, over a type `α`, presented_group constructs the group with
generators `x : α` and relations `rels` as a quotient of free_group `α`.-/
def presented_group (rels : set (free_group α)) : Type :=
quotient_group.quotient $ subgroup.normal_closure rels

namespace presented_group

instance (rels : set (free_group α)) : group (presented_group (rels)) :=
quotient_group.quotient.group _

/-- `of` is the canonical map from `α` to a presented group with generators `x : α`. The term `x` is
mapped to the equivalence class of the image of `x` in `free_group α`. -/
def of {rels : set (free_group α)} (x : α) : presented_group rels :=
quotient_group.mk (free_group.of x)

section to_group

/-
Presented groups satisfy a universal property. If `G` is a group and `f : α → G` is a map such that
the images of `f` satisfy all the given relations, then `f` extends uniquely to a group homomorphism
from `presented_group rels` to `G`.
-/

variables {G : Type} [group G] {f : α → G} {rels : set (free_group α)}

local notation `F` := free_group.lift f

variable (h : ∀ r ∈ rels, F r = 1)

lemma closure_rels_subset_ker : subgroup.normal_closure rels ≤ monoid_hom.ker F :=
subgroup.normal_closure_le_normal (λ x w, (monoid_hom.mem_ker _).2 (h x w))

lemma to_group_eq_one_of_mem_closure : ∀ x ∈ subgroup.normal_closure rels, F x = 1 :=
λ x w, (monoid_hom.mem_ker _).1 $ closure_rels_subset_ker h w

/-- The extension of a map `f : α → G` that satisfies the given relations to a group homomorphism
from `presented_group rels → G`. -/
def to_group : presented_group rels →* G :=
quotient_group.lift (subgroup.normal_closure rels) F (to_group_eq_one_of_mem_closure h)

@[simp] lemma to_group.of {x : α} : to_group h (of x) = f x := free_group.lift.of

theorem to_group.unique (g : presented_group rels →* G)
  (hg : ∀ x : α, g (of x) = f x) : ∀ {x}, g x = to_group h x :=
λ x, quotient_group.induction_on x
    (λ _, free_group.lift.unique (g.comp (quotient_group.mk' _)) hg)

end to_group

instance (rels : set (free_group α)) : inhabited (presented_group rels) := ⟨1⟩

end presented_group
