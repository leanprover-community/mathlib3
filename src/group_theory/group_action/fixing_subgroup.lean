/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import group_theory.subgroup.basic
import group_theory.group_action.basic
import order.order_dual

/-!

# Fixing submonoid, fixing subgroup of an action

In the presence of of an action of a monoid or a group,
this file defines the fixing submonoid or the fixing subgroup,
and relates it to the set of fixed points via a Galois connection.

## Main definitions

* `fixing_submonoid M s` :
in the presence of `mul_action M α` (with `monoid M`)
it is the `submonoid M` consisting of elements which fix `s : set α` pointwise.

* `fixing_submonoid_fixed_points_connection M α` is the `galois_connection`
that relates `fixing_submonoid` with `fixed_points`.

* `fixing_submonoid_of_union` and `fixing_submonoid_of_Union` are consequences
of the Galois connection, as well as `fixed_points_of_sup` and `fixed_points_of_supr`.

* `fixing_subgroup M s` :
in the presence of `mul_action M α` (with `group M`)
it is the `subgroup M` consisting of elements which fix `s : set α` pointwise.

* `fixing_subgroup_fixed_points_connection M α` is the `galois_connection`
that relates `fixing_subgroup` with `fixed_points`.

* `fixing_subgroup_of_union` and `fixing_subgroup_of_Union` are consequences
of the Galois connection,
as well as `fixed_points_of_group_of_sup` and `fixed_points_of_group_of_supr`.

* The file starts with some lemmas that allow to rewrite `antitone` into `monotone`
in various cases.
Apparently the `monotone.dual` (and analogues) were not sufficient, so I wrote `monotone.dual_iff`
that works in both directions.

TODO :

* Adjust names as needed

* Decide what needs to be done with the antitonicity section. In particular, the
proofs need two directions, but the proof term is exactly the same (up to types).

* Maybe other lemmas are useful

* Treat semigroups ?

-/

section antitonicity

universes u v
variables {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} {s : set α}

open order_dual

lemma forall₂_swap {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₁ → Sort*}
  {p : Π i₁, κ₁ i₁ → Π i₂, κ₂ i₂ → Prop} :
  (∀ i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ ∀ i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ :=
⟨λ h i₂ j₂ i₁ j₁, h i₁ j₁ i₂ j₂, λ h i₁ j₁ i₂ j₂, h i₂ j₂ i₁ j₁⟩

-- It's not better with this
lemma forall₂_swap' {ι₁ ι₂ ι₃ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₁ → Sort*}
  {p : Π i₁, κ₁ i₁ → Π i₂, κ₂ i₂ → ι₃ → Prop} :
  (∀ i₁ j₁ i₂ j₂ i₃, p i₁ j₁ i₂ j₂ i₃) ↔ ∀ i₂ j₂ i₁ j₁ i₃, p i₁ j₁ i₂ j₂ i₃ :=
⟨λ h i₂ j₂ i₁ j₁ i₃, h i₁ j₁ i₂ j₂ i₃, λ h i₁ j₁ i₂ j₂ i₃, h i₂ j₂ i₁ j₁ i₃⟩

@[simp] lemma antitone_to_dual_comp_iff : antitone (to_dual ∘ f) ↔ monotone f :=
iff.rfl

@[simp] lemma monotone_comp_of_dual_iff : monotone (f ∘ of_dual) ↔ antitone f :=
forall_swap

@[simp] lemma antitone_on_to_dual_comp_iff : antitone_on (to_dual ∘ f) s ↔ monotone_on f s :=
iff.rfl

@[simp] lemma monotone_on_comp_of_dual_iff : monotone_on (f ∘ of_dual) s ↔ antitone_on f s :=
-- forall₂_swap /- Does not work -/
begin
split; exact λ hf a ha b hb h, hf hb ha h
end

end antitonicity

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
  m ∈ fixing_submonoid M s ↔ ∀ (y : α) (hy : y ∈ s), m • y = y :=
⟨λ hg y hy, hg ⟨y, hy⟩, λ h ⟨y, hy⟩, h y hy⟩

variable (α)

/-- The Galois connection between fixing submonoids and fixed points of a monoid action -/
theorem fixing_submonoid_fixed_points_connection : galois_connection
  (order_dual.to_dual ∘ (λ s : set α, fixing_submonoid M s))
  ((λ P : submonoid M, (fixed_points P α)) ∘ order_dual.of_dual) :=
λ s P, ⟨λ h s hs p, h p.2 ⟨s, hs⟩, λ h p hp s, h s.2 ⟨p, hp⟩⟩

lemma fixing_submonoid_is_antitone : antitone (λ (s : set α), fixing_submonoid M s) :=
galois_connection.monotone_l (fixing_submonoid_fixed_points_connection M α)

lemma fixed_points_is_antitone :
  antitone (λ (P : submonoid M), fixed_points P α) :=
(fixing_submonoid_fixed_points_connection M α).monotone_u.dual_left

/-- Fixing submonoid of union is intersection -/
lemma fixing_submonoid_of_union {s t : set α} :
  fixing_submonoid M (s ∪ t) = (fixing_submonoid M s) ⊓ (fixing_submonoid M t) :=
galois_connection.l_sup (fixing_submonoid_fixed_points_connection M α)

/-- Fixing submonoid of Union is intersection -/
lemma fixing_submonoid_Union {ι : Sort*} {s : ι → set α} :
  fixing_submonoid M (⋃ i, s i) = ⨅ i, fixing_submonoid M (s i) :=
galois_connection.l_supr (fixing_submonoid_fixed_points_connection M α)

/-- Fixed points of sup of submonoids is intersection -/
lemma fixed_points_of_sup {P Q : submonoid M} :
  fixed_points (P ⊔ Q) α = fixed_points P α ∩ fixed_points Q α :=
  galois_connection.u_inf (fixing_submonoid_fixed_points_connection M α)

/-- Fixed points of supr of submonoids is intersection -/
lemma fixed_points_supr {ι : Sort*} {P : ι → submonoid M} :
  fixed_points (supr P : submonoid M) α =
    infi (λ i, (fixed_points (P i) α)) :=
  galois_connection.u_infi (fixing_submonoid_fixed_points_connection M α)

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
  m ∈ fixing_subgroup M s ↔ ∀ (y : α) (hy : y ∈ s), m • y = y :=
⟨λ hg y hy, hg ⟨y, hy⟩, λ h ⟨y, hy⟩, h y hy⟩

variable (α)

/-- The Galois connection between fixing subgroups and fixed points of a group action -/
lemma fixing_subgroup_fixed_points_connection : galois_connection
  (order_dual.to_dual ∘ (λ s : set α, fixing_subgroup M s))
  ((λ P : subgroup M, (fixed_points P α)) ∘ order_dual.of_dual) :=
λ s P, ⟨λ h s hs p, h p.2 ⟨s, hs⟩, λ h p hp s, h s.2 ⟨p, hp⟩⟩

lemma fixing_subgroup_is_antitone : antitone (λ (s : set α), fixing_subgroup M s) :=
galois_connection.monotone_l (fixing_subgroup_fixed_points_connection M α)

lemma fixed_points_of_group_is_antitone :
  antitone (λ (P : subgroup M), fixed_points P α) :=
(fixing_subgroup_fixed_points_connection M α).monotone_u.dual_left


/-- Fixing subgroup of union is intersection -/
lemma fixing_subgroup_of_union {s t : set α} :
  fixing_subgroup M (s ∪ t) = (fixing_subgroup M s) ⊓ (fixing_subgroup M t) :=
galois_connection.l_sup (fixing_subgroup_fixed_points_connection M α)

/-- Fixing subgroup of Union is intersection -/
lemma fixing_subgroup_of_Union {ι : Type*} {s : ι → set α} :
  fixing_subgroup M (⋃ (i : ι), s i) = infi (λ i, (fixing_subgroup M (s i))) :=
galois_connection.l_supr (fixing_subgroup_fixed_points_connection M α)

/-- Fixed points of sup of subgroups is intersection -/
lemma fixed_points_of_group_of_sup {P Q : subgroup M} :
  fixed_points (P ⊔ Q : subgroup M) α = (fixed_points P α) ⊓ (fixed_points Q α) :=
galois_connection.u_inf (fixing_subgroup_fixed_points_connection M α)

/-- Fixed points of supr of subgroups is intersection -/
lemma fixed_points_of_group_of_supr {ι : Type*} {P : ι → subgroup M} :
  fixed_points (supr P : subgroup M) α = infi (λ i, (fixed_points (P i) α)) :=
galois_connection.u_infi (fixing_subgroup_fixed_points_connection M α)

end group
