/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.subgroup.pointwise
import linear_algebra.span

/-! # Pointwise instances on `submodule`s

This file provides:

* `submodule.has_pointwise_neg`

and the actions

* `submodule.pointwise_distrib_mul_action`
* `submodule.pointwise_mul_action_with_zero`

which matches the action of `mul_action_set`.

These actions are available in the `pointwise` locale.

## Implementation notes

Most of the lemmas in this file are direct copies of lemmas from
`group_theory/submonoid/pointwise.lean`.
-/

variables {α : Type*} {R : Type*} {M : Type*}

open_locale pointwise

namespace submodule

section neg

section semiring
variables [semiring R] [add_comm_group M] [module R M]

/-- The submodule with every element negated. Note if `R` is a ring and not just a semiring, this
is a no-op, as shown by `submodule.neg_eq_self`.

Recall that When `R` is the semiring corresponding to the nonnegative elements of `R'`,
`submodule R' M` is the type of cones of `M`. This instance reflects such cones about `0`.

This is available as an instance in the `pointwise` locale. -/
protected def has_pointwise_neg : has_neg (submodule R M) :=
{ neg := λ p,
  { carrier := -(p : set M),
    smul_mem' := λ r m hm, set.mem_neg.2 $ smul_neg r m ▸ p.smul_mem r $ set.mem_neg.1 hm,
    ..(- p.to_add_submonoid) } }

localized "attribute [instance] submodule.has_pointwise_neg" in pointwise
open_locale pointwise

@[simp] lemma coe_set_neg (S : submodule R M) : ↑(-S) = -(S : set M) := rfl

@[simp] lemma neg_to_add_submonoid (S : submodule R M) :
  (-S).to_add_submonoid = -S.to_add_submonoid := rfl

@[simp] lemma mem_neg {g : M} {S : submodule R M} : g ∈ -S ↔ -g ∈ S := iff.rfl

/-- `submodule.has_pointwise_neg` is involutive.

This is available as an instance in the `pointwise` locale. -/
protected def has_involutive_pointwise_neg : has_involutive_neg (submodule R M) :=
{ neg := has_neg.neg,
  neg_neg := λ S, set_like.coe_injective $ neg_neg _ }

localized "attribute [instance] submodule.has_involutive_pointwise_neg" in pointwise

@[simp] lemma neg_le_neg (S T : submodule R M) : -S ≤ -T ↔ S ≤ T :=
set_like.coe_subset_coe.symm.trans set.neg_subset_neg

lemma neg_le (S T : submodule R M) : -S ≤ T ↔ S ≤ -T :=
set_like.coe_subset_coe.symm.trans set.neg_subset

/-- `submodule.has_pointwise_neg` as an order isomorphism. -/
def neg_order_iso : submodule R M ≃o submodule R M :=
{ to_equiv := equiv.neg _,
  map_rel_iff' := neg_le_neg }

lemma closure_neg (s : set M) : span R (-s) = -(span R s) :=
begin
  apply le_antisymm,
  { rw [span_le, coe_set_neg, ←set.neg_subset, neg_neg],
    exact subset_span },
  { rw [neg_le, span_le, coe_set_neg, ←set.neg_subset],
    exact subset_span }
end

@[simp]
lemma neg_inf (S T : submodule R M) : -(S ⊓ T) = (-S) ⊓ (-T) :=
set_like.coe_injective set.inter_neg

@[simp]
lemma neg_sup (S T : submodule R M) : -(S ⊔ T) = (-S) ⊔ (-T) :=
(neg_order_iso : submodule R M ≃o submodule R M).map_sup S T

@[simp]
lemma neg_bot : -(⊥ : submodule R M) = ⊥ :=
set_like.coe_injective $ (set.neg_singleton 0).trans $ congr_arg _ neg_zero

@[simp]
lemma neg_top : -(⊤ : submodule R M) = ⊤ :=
set_like.coe_injective $ set.neg_univ

@[simp]
lemma neg_infi {ι : Sort*} (S : ι → submodule R M) : -(⨅ i, S i) = ⨅ i, -S i :=
(neg_order_iso : submodule R M ≃o submodule R M).map_infi _

@[simp]
lemma neg_supr {ι : Sort*} (S : ι → submodule R M) : -(⨆ i, S i) = ⨆ i, -(S i) :=
(neg_order_iso : submodule R M ≃o submodule R M).map_supr _

end semiring

open_locale pointwise

@[simp] lemma neg_eq_self [ring R] [add_comm_group M] [module R M] (p : submodule R M) : -p = p :=
ext $ λ _, p.neg_mem_iff

end neg

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

instance pointwise_central_scalar [distrib_mul_action αᵐᵒᵖ M] [smul_comm_class αᵐᵒᵖ R M]
  [is_central_scalar α M] :
  is_central_scalar α (submodule R M) :=
⟨λ a S, congr_arg (λ f, S.map f) $ linear_map.ext $ by exact op_smul_eq_smul _⟩

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
