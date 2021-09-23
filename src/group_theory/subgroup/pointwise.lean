/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.subgroup.basic
import group_theory.submonoid.pointwise

/-! # Pointwise instances on `subgroup`s

This file provides the actions

* `subgroup.pointwise_mul_action`
* `add_subgroup.pointwise_mul_action`

which matches the action of `mul_action_set`.

These actions are available in the `pointwise` locale.
-/

variables {α : Type*} {G : Type*} {A : Type*} [group G] [add_group A]

namespace subgroup

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

end subgroup

namespace add_subgroup

variables [monoid α] [distrib_mul_action α A]

/-- The action on a additive subgroup corresponding to applying the action to every element.

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

end add_subgroup
