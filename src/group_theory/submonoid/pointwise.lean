/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.submonoid.operations
import algebra.pointwise

/-! # Pointwise instances on `submonoid`s and `add_submonoid`s

This file provides the actions

* `submonoid.pointwise_mul_action`
* `add_submonoid.pointwise_mul_action`

which matches the action of `mul_action_set`.

These actions are available in the `pointwise` locale.

## Implementation notes

Most of the lemmas in this file are direct copies of lemmas from `algebra/pointwise.lean`.
While the statements of these lemmas are defeq, we repeat them here due to them not being
syntactically equal. Before adding new lemmas here, consider if they would also apply to the action
on `set`s.

-/

variables {α : Type*} {M : Type*} {A : Type*} [monoid M] [add_monoid A]

namespace submonoid

section monoid
variables [monoid α] [mul_distrib_mul_action α M]

/-- The action on a submonoid corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : mul_action α (submonoid M) :=
{ smul := λ a S, S.map (mul_distrib_mul_action.to_monoid_End _ _ a),
  one_smul := λ S, (congr_arg (λ f, S.map f) (monoid_hom.map_one _)).trans S.map_id,
  mul_smul := λ a₁ a₂ S,
    (congr_arg (λ f, S.map f) (monoid_hom.map_mul _ _ _)).trans (S.map_map _ _).symm,}

localized "attribute [instance] submonoid.pointwise_mul_action" in pointwise
open_locale pointwise

@[simp] lemma coe_pointwise_smul (a : α) (S : submonoid M) : ↑(a • S) = a • (S : set M) := rfl

lemma smul_mem_pointwise_smul (m : M) (a : α) (S : submonoid M) : m ∈ S → a • m ∈ a • S :=
(set.smul_mem_smul_set : _ → _ ∈ a • (S : set M))

end monoid

section group
variables [group α] [mul_distrib_mul_action α M]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff {a : α} {S : submonoid M} {x : M} :
  a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff

lemma mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : submonoid M} {x : M} :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem

lemma mem_inv_pointwise_smul_iff {a : α} {S : submonoid M} {x : M} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff

@[simp] lemma pointwise_smul_le_pointwise_smul_iff {a : α} {S T : submonoid M} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff

lemma pointwise_smul_subset_iff {a : α} {S T : submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff

lemma subset_pointwise_smul_iff {a : α} {S T : submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff

end group

section group_with_zero
variables [group_with_zero α] [mul_distrib_mul_action α M]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff' {a : α} (ha : a ≠ 0) (S : submonoid M)
  (x : M) : a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff' ha (S : set M) x

lemma mem_pointwise_smul_iff_inv_smul_mem' {a : α} (ha : a ≠ 0) (S : submonoid M) (x : M) :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem' ha (S : set M) x

lemma mem_inv_pointwise_smul_iff' {a : α} (ha : a ≠ 0) (S : submonoid M) (x : M) :
  x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff' ha (S : set M) x

@[simp] lemma pointwise_smul_le_pointwise_smul_iff' {a : α} (ha : a ≠ 0) {S T : submonoid M} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff' ha

lemma pointwise_smul_le_iff' {a : α} (ha : a ≠ 0) {S T : submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff' ha

lemma le_pointwise_smul_iff' {a : α} (ha : a ≠ 0) {S T : submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff' ha

end group_with_zero

end submonoid

namespace add_submonoid

section monoid
variables [monoid α] [distrib_mul_action α A]

/-- The action on an additive submonoid corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : mul_action α (add_submonoid A) :=
{ smul := λ a S, S.map (distrib_mul_action.to_add_monoid_End _ _ a),
  one_smul := λ S, (congr_arg (λ f, S.map f) (monoid_hom.map_one _)).trans S.map_id,
  mul_smul := λ a₁ a₂ S,
    (congr_arg (λ f, S.map f) (monoid_hom.map_mul _ _ _)).trans (S.map_map _ _).symm,}

localized "attribute [instance] add_submonoid.pointwise_mul_action" in pointwise
open_locale pointwise

@[simp] lemma coe_pointwise_smul (a : α) (S : add_submonoid A) : ↑(a • S) = a • (S : set A) := rfl

lemma smul_mem_pointwise_smul (m : A) (a : α) (S : add_submonoid A) : m ∈ S → a • m ∈ a • S :=
(set.smul_mem_smul_set : _ → _ ∈ a • (S : set A))

end monoid

section group
variables [group α] [distrib_mul_action α A]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff {a : α} {S : add_submonoid A} {x : A} :
  a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff

lemma mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : add_submonoid A} {x : A} :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem

lemma mem_inv_pointwise_smul_iff {a : α} {S : add_submonoid A} {x : A} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff

@[simp] lemma pointwise_smul_le_pointwise_smul_iff {a : α} {S T : add_submonoid A} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff

lemma pointwise_smul_le_iff {a : α} {S T : add_submonoid A} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff

lemma le_pointwise_smul_iff {a : α} {S T : add_submonoid A} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff

end group

section group_with_zero
variables [group_with_zero α] [distrib_mul_action α A]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff' {a : α} (ha : a ≠ 0) (S : add_submonoid A)
  (x : A) : a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff' ha (S : set A) x

lemma mem_pointwise_smul_iff_inv_smul_mem' {a : α} (ha : a ≠ 0) (S : add_submonoid A) (x : A) :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem' ha (S : set A) x

lemma mem_inv_pointwise_smul_iff' {a : α} (ha : a ≠ 0) (S : add_submonoid A) (x : A) :
  x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff' ha (S : set A) x

@[simp] lemma pointwise_smul_le_pointwise_smul_iff' {a : α} (ha : a ≠ 0) {S T : add_submonoid A} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff' ha

lemma pointwise_smul_le_iff' {a : α} (ha : a ≠ 0) {S T : add_submonoid A} :
  a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff' ha

lemma le_pointwise_smul_iff' {a : α} (ha : a ≠ 0) {S T : add_submonoid A} :
  S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff' ha

end group_with_zero

end add_submonoid
