/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import ring_theory.subsemiring.basic
import algebra.group_ring_action
import algebra.pointwise

/-! # Pointwise instances on `subsemiring`s

This file provides the action `subsemiring.pointwise_mul_action` which matches the action of
`mul_action_set`.

This actions is available in the `pointwise` locale.

## Implementation notes

This file is almost identical to `group_theory/submonoid/pointwise.lean`. Where possible, try to
keep them in sync.
-/

variables {M R : Type*}

namespace subsemiring

section monoid
variables [monoid M] [semiring R] [mul_semiring_action M R]

/-- The action on a subsemiring corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : mul_action M (subsemiring R) :=
{ smul := λ a S, S.map (mul_semiring_action.to_ring_hom _ _ a),
  one_smul := λ S,
    (congr_arg (λ f, S.map f) (ring_hom.ext $ by exact one_smul M)).trans S.map_id,
  mul_smul := λ a₁ a₂ S,
    (congr_arg (λ f, S.map f) (ring_hom.ext $ by exact mul_smul _ _)).trans (S.map_map _ _).symm }

localized "attribute [instance] subsemiring.pointwise_mul_action" in pointwise
open_locale pointwise

lemma pointwise_smul_def {a : M} (S : subsemiring R) :
  a • S = S.map (mul_semiring_action.to_ring_hom _ _ a) := rfl

@[simp] lemma coe_pointwise_smul (m : M) (S : subsemiring R) : ↑(m • S) = m • (S : set R) := rfl

@[simp] lemma pointwise_smul_to_add_submonoid (m : M) (S : subsemiring R) :
  (m • S).to_add_submonoid = m • S.to_add_submonoid := rfl

lemma smul_mem_pointwise_smul (m : M) (r : R) (S : subsemiring R) : r ∈ S → m • r ∈ m • S :=
(set.smul_mem_smul_set : _ → _ ∈ m • (S : set R))

lemma mem_smul_pointwise_iff_exists (m : M) (r : R) (S : subsemiring R) :
  r ∈ m • S ↔ ∃ (s : R), s ∈ S ∧ m • s = r :=
(set.mem_smul_set : r ∈ m • (S : set R) ↔ _)

instance pointwise_central_scalar [mul_semiring_action Mᵐᵒᵖ R] [is_central_scalar M R] :
  is_central_scalar M (subsemiring R) :=
⟨λ a S, congr_arg (λ f, S.map f) $ ring_hom.ext $ by exact op_smul_eq_smul _⟩

end monoid

section group
variables [group M] [semiring R] [mul_semiring_action M R]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff {a : M} {S : subsemiring R} {x : R} :
  a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff

lemma mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : subsemiring R} {x : R} :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem

lemma mem_inv_pointwise_smul_iff {a : M} {S : subsemiring R} {x : R} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff

@[simp] lemma pointwise_smul_le_pointwise_smul_iff {a : M} {S T : subsemiring R} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff

lemma pointwise_smul_subset_iff {a : M} {S T : subsemiring R} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff

lemma subset_pointwise_smul_iff {a : M} {S T : subsemiring R} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff

/-! TODO: add `equiv_smul` like we have for subgroup. -/

end group

section group_with_zero
variables [group_with_zero M] [semiring R] [mul_semiring_action M R]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : subsemiring R)
  (x : R) : a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff₀ ha (S : set R) x

lemma mem_pointwise_smul_iff_inv_smul_mem₀ {a : M} (ha : a ≠ 0) (S : subsemiring R) (x : R) :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem₀ ha (S : set R) x

lemma mem_inv_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : subsemiring R) (x : R) :
  x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff₀ ha (S : set R) x

@[simp] lemma pointwise_smul_le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : subsemiring R} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff₀ ha

lemma pointwise_smul_le_iff₀ {a : M} (ha : a ≠ 0) {S T : subsemiring R} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff₀ ha

lemma le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : subsemiring R} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff₀ ha

end group_with_zero

end subsemiring
