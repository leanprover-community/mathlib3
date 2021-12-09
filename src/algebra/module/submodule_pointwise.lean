/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.subgroup.pointwise
import linear_algebra.basic

/-! # Pointwise instances on `submodule`s

This file provides the actions

* `submodule.pointwise_distrib_mul_action`
* `submodule.pointwise_mul_action_with_zero`

which matches the action of `mul_action_set`.

These actions are available in the `pointwise` locale.
-/

namespace submodule

variables {α : Type*} {R : Type*} {M : Type*}
variables [semiring R] [add_comm_monoid M] [module R M]


instance pointwise_add_comm_monoid : add_comm_monoid (submodule R M) :=
{ add := (⊔),
  add_assoc := λ _ _ _, sup_assoc,
  zero := ⊥,
  zero_add := λ _, bot_sup_eq,
  add_zero := λ _, sup_bot_eq,
  add_comm := λ _ _, sup_comm }

@[simp] lemma add_eq_sup (p q : submodule R M) : p + q = p ⊔ q := rfl
@[simp] lemma zero_eq_bot : (0 : submodule R M) = ⊥ := rfl


section
variables [monoid α] [distrib_mul_action α M] [smul_comm_class α R M]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_distrib_mul_action : distrib_mul_action α (submodule R M) :=
{ smul := λ a S, S.map (distrib_mul_action.to_linear_map _ _ a),
  one_smul := λ S,
    (congr_arg (λ f, S.map f) (linear_map.ext $ by exact one_smul α)).trans S.map_id,
  mul_smul := λ a₁ a₂ S,
    (congr_arg (λ f : M →ₗ[R] M, S.map f) (linear_map.ext $ by exact mul_smul _ _)).trans
      (S.map_comp _ _),
  smul_zero := λ a, map_bot _,
  smul_add := λ a S₁ S₂, map_sup _ _ _ }

localized "attribute [instance] submodule.pointwise_distrib_mul_action" in pointwise
open_locale pointwise

@[simp] lemma coe_pointwise_smul (a : α) (S : submodule R M) : ↑(a • S) = a • (S : set M) := rfl

@[simp] lemma pointwise_smul_to_add_submonoid (a : α) (S : submodule R M) :
  (a • S).to_add_submonoid = a • S.to_add_submonoid := rfl

@[simp] lemma pointwise_smul_to_add_subgroup {R M : Type*}
  [ring R] [add_comm_group M] [distrib_mul_action α M] [module R M] [smul_comm_class α R M]
  (a : α) (S : submodule R M) :
  (a • S).to_add_subgroup = a • S.to_add_subgroup := rfl

lemma smul_mem_pointwise_smul (m : M) (a : α) (S : submodule R M) : m ∈ S → a • m ∈ a • S :=
(set.smul_mem_smul_set : _ → _ ∈ a • (S : set M))

@[simp] lemma smul_le_self_of_tower {α : Type*}
  [semiring α] [module α R] [module α M] [smul_comm_class α R M] [is_scalar_tower α R M]
  (a : α) (S : submodule R M) : a • S ≤ S :=
begin
  rintro y ⟨x, hx, rfl⟩,
  exact smul_of_tower_mem _ a hx,
end

end

section
variables [semiring α] [module α M] [smul_comm_class α R M]
/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale.

This is a stronger version of `submodule.pointwise_distrib_mul_action`. Note that `add_smul` does
not hold so this cannot be stated as a `module`. -/
protected def pointwise_mul_action_with_zero : mul_action_with_zero α (submodule R M) :=
{ zero_smul := λ S,
    (congr_arg (λ f : M →ₗ[R] M, S.map f) (linear_map.ext $ by exact zero_smul α)).trans S.map_zero,
  .. submodule.pointwise_distrib_mul_action }

localized "attribute [instance] submodule.pointwise_mul_action_with_zero" in pointwise

end

end submodule
