/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.subgroup.basic
import group_theory.submonoid.pointwise

/-! # Pointwise instances on `subgroup` and `add_subgroup`s

This file provides the actions

* `subgroup.pointwise_mul_action`
* `add_subgroup.pointwise_mul_action`

which matches the action of `mul_action_set`.

These actions are available in the `pointwise` locale.

## Implementation notes

This file is almost identical to `group_theory/submonoid/pointwise.lean`. Where possible, try to
keep them in sync.
-/

variables {α : Type*} {G : Type*} {A : Type*} [group G] [add_group A]

namespace subgroup

section monoid
variables [monoid α] [mul_distrib_mul_action α G]

/-- The action on a subgroup corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : mul_action α (subgroup G) :=
{ smul := λ a S, S.map (mul_distrib_mul_action.to_monoid_End _ _ a),
  one_smul := λ S, (congr_arg (λ f, S.map f) (monoid_hom.map_one _)).trans S.map_id,
  mul_smul := λ a₁ a₂ S,
    (congr_arg (λ f, S.map f) (monoid_hom.map_mul _ _ _)).trans (S.map_map _ _).symm,}

localized "attribute [instance] subgroup.pointwise_mul_action" in pointwise
open_locale pointwise

@[simp] lemma coe_pointwise_smul (a : α) (S : subgroup G) : ↑(a • S) = a • (S : set G) := rfl

@[simp] lemma pointwise_smul_to_submonoid (a : α) (S : subgroup G) :
  (a • S).to_submonoid = a • S.to_submonoid := rfl

lemma smul_mem_pointwise_smul (m : G) (a : α) (S : subgroup G) : m ∈ S → a • m ∈ a • S :=
(set.smul_mem_smul_set : _ → _ ∈ a • (S : set G))

end monoid

section group
variables [group α] [mul_distrib_mul_action α G]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff {a : α} {S : subgroup G} {x : G} :
  a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff

lemma mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : subgroup G} {x : G} :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem

lemma mem_inv_pointwise_smul_iff {a : α} {S : subgroup G} {x : G} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff

@[simp] lemma pointwise_smul_le_pointwise_smul_iff {a : α} {S T : subgroup G} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff

lemma pointwise_smul_subset_iff {a : α} {S T : subgroup G} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff

lemma subset_pointwise_smul_iff {a : α} {S T : subgroup G} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff

end group

section group_with_zero
variables [group_with_zero α] [mul_distrib_mul_action α G]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : subgroup G)
  (x : G) : a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff₀ ha (S : set G) x

lemma mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : subgroup G) (x : G) :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem₀ ha (S : set G) x

lemma mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : subgroup G) (x : G) :
  x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff₀ ha (S : set G) x

@[simp] lemma pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : subgroup G} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff₀ ha

lemma pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : subgroup G} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff₀ ha

lemma le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : subgroup G} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff₀ ha

end group_with_zero

end subgroup

namespace add_subgroup

section monoid
variables [monoid α] [distrib_mul_action α A]

/-- The action on an additive subgroup corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : mul_action α (add_subgroup A) :=
{ smul := λ a S, S.map (distrib_mul_action.to_add_monoid_End _ _ a),
  one_smul := λ S, (congr_arg (λ f, S.map f) (monoid_hom.map_one _)).trans S.map_id,
  mul_smul := λ a₁ a₂ S,
    (congr_arg (λ f, S.map f) (monoid_hom.map_mul _ _ _)).trans (S.map_map _ _).symm,}

localized "attribute [instance] add_subgroup.pointwise_mul_action" in pointwise
open_locale pointwise

@[simp] lemma coe_pointwise_smul (a : α) (S : add_subgroup A) : ↑(a • S) = a • (S : set A) := rfl

@[simp] lemma pointwise_smul_to_add_submonoid (a : α) (S : add_subgroup A) :
  (a • S).to_add_submonoid = a • S.to_add_submonoid := rfl

lemma smul_mem_pointwise_smul (m : A) (a : α) (S : add_subgroup A) : m ∈ S → a • m ∈ a • S :=
(set.smul_mem_smul_set : _ → _ ∈ a • (S : set A))

end monoid

section group
variables [group α] [distrib_mul_action α A]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff {a : α} {S : add_subgroup A} {x : A} :
  a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff

lemma mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : add_subgroup A} {x : A} :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem

lemma mem_inv_pointwise_smul_iff {a : α} {S : add_subgroup A} {x : A} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff

@[simp] lemma pointwise_smul_le_pointwise_smul_iff {a : α} {S T : add_subgroup A} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff

lemma pointwise_smul_le_iff {a : α} {S T : add_subgroup A} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff

lemma le_pointwise_smul_iff {a : α} {S T : add_subgroup A} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff

end group

section group_with_zero
variables [group_with_zero α] [distrib_mul_action α A]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : add_subgroup A)
  (x : A) : a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff₀ ha (S : set A) x

lemma mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : add_subgroup A) (x : A) :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem₀ ha (S : set A) x

lemma mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : add_subgroup A) (x : A) :
  x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff₀ ha (S : set A) x

@[simp] lemma pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : add_subgroup A} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff₀ ha

lemma pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : add_subgroup A} :
  a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff₀ ha

lemma le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : add_subgroup A} :
  S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff₀ ha

end group_with_zero

end add_subgroup
