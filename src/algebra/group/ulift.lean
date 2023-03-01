/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.int.cast.defs
import algebra.hom.equiv.basic
import algebra.group_with_zero.inj_surj

/-!
# `ulift` instances for groups and monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for group, monoid, semigroup and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We use `tactic.pi_instance_derive_field`, even though it wasn't intended for this purpose,
which seems to work fine.

We also provide `ulift.mul_equiv : ulift R ≃* R` (and its additive analogue).
-/

universes u v
variables {α : Type u} {β : Type*} {x y : ulift.{v} α}

namespace ulift

@[to_additive] instance has_one [has_one α] : has_one (ulift α) := ⟨⟨1⟩⟩
@[simp, to_additive] lemma one_down [has_one α] : (1 : ulift α).down = 1 := rfl

@[to_additive] instance has_mul [has_mul α] : has_mul (ulift α) := ⟨λ f g, ⟨f.down * g.down⟩⟩
@[simp, to_additive] lemma mul_down [has_mul α] : (x * y).down = x.down * y.down := rfl

@[to_additive] instance has_div [has_div α] : has_div (ulift α) := ⟨λ f g, ⟨f.down / g.down⟩⟩
@[simp, to_additive] lemma div_down [has_div α] : (x / y).down = x.down / y.down := rfl

@[to_additive] instance has_inv [has_inv α] : has_inv (ulift α) := ⟨λ f, ⟨f.down⁻¹⟩⟩
@[simp, to_additive] lemma inv_down [has_inv α] : x⁻¹.down = (x.down)⁻¹ := rfl

@[to_additive]
instance has_smul [has_smul α β] : has_smul α (ulift β) := ⟨λ n x, up (n • x.down)⟩
@[simp, to_additive]
lemma smul_down [has_smul α β] (a : α) (b : ulift.{v} β) : (a • b).down = a • b.down := rfl

@[to_additive has_smul, to_additive_reorder 1]
instance has_pow [has_pow α β] : has_pow (ulift α) β := ⟨λ x n, up (x.down ^ n)⟩
@[simp, to_additive smul_down, to_additive_reorder 1]
lemma pow_down [has_pow α β] (a : ulift.{v} α) (b : β) : (a ^ b).down = a.down ^ b := rfl

/--
The multiplicative equivalence between `ulift α` and `α`.
-/
@[to_additive "The additive equivalence between `ulift α` and `α`."]
def _root_.mul_equiv.ulift [has_mul α] : ulift α ≃* α :=
{ map_mul' := λ x y, rfl,
  .. equiv.ulift }

@[to_additive]
instance semigroup [semigroup α] : semigroup (ulift α) :=
mul_equiv.ulift.injective.semigroup _ $ λ x y, rfl

@[to_additive]
instance comm_semigroup [comm_semigroup α] : comm_semigroup (ulift α) :=
equiv.ulift.injective.comm_semigroup _ $ λ x y, rfl

@[to_additive]
instance mul_one_class [mul_one_class α] : mul_one_class (ulift α) :=
equiv.ulift.injective.mul_one_class _ rfl $ λ x y, rfl

instance mul_zero_one_class [mul_zero_one_class α] : mul_zero_one_class (ulift α) :=
equiv.ulift.injective.mul_zero_one_class _ rfl rfl $ λ x y, rfl

@[to_additive]
instance monoid [monoid α] : monoid (ulift α) :=
equiv.ulift.injective.monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)

instance add_monoid_with_one [add_monoid_with_one α] : add_monoid_with_one (ulift α) :=
{ nat_cast := λ n, ⟨n⟩,
  nat_cast_zero := congr_arg ulift.up nat.cast_zero,
  nat_cast_succ := λ n, congr_arg ulift.up (nat.cast_succ _),
  .. ulift.has_one, .. ulift.add_monoid }

@[simp] lemma nat_cast_down [add_monoid_with_one α] (n : ℕ) :
  (n : ulift α).down = n :=
rfl

@[to_additive]
instance comm_monoid [comm_monoid α] : comm_monoid (ulift α) :=
equiv.ulift.injective.comm_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)

instance monoid_with_zero [monoid_with_zero α] : monoid_with_zero (ulift α) :=
equiv.ulift.injective.monoid_with_zero _ rfl rfl (λ _ _, rfl) (λ _ _, rfl)

instance comm_monoid_with_zero [comm_monoid_with_zero α] : comm_monoid_with_zero (ulift α) :=
equiv.ulift.injective.comm_monoid_with_zero _ rfl rfl (λ _ _, rfl) (λ _ _, rfl)

@[to_additive]
instance div_inv_monoid [div_inv_monoid α] : div_inv_monoid (ulift α) :=
equiv.ulift.injective.div_inv_monoid _ rfl (λ _ _, rfl) (λ _, rfl)
  (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

@[to_additive]
instance group [group α] : group (ulift α) :=
equiv.ulift.injective.group _ rfl (λ _ _, rfl) (λ _, rfl)
  (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance add_group_with_one [add_group_with_one α] : add_group_with_one (ulift α) :=
{ int_cast := λ n, ⟨n⟩,
  int_cast_of_nat := λ n, congr_arg ulift.up (int.cast_of_nat _),
  int_cast_neg_succ_of_nat := λ n, congr_arg ulift.up (int.cast_neg_succ_of_nat _),
  .. ulift.add_monoid_with_one, .. ulift.add_group }

@[simp] lemma int_cast_down [add_group_with_one α] (n : ℤ) :
  (n : ulift α).down = n :=
rfl

@[to_additive]
instance comm_group [comm_group α] : comm_group (ulift α) :=
equiv.ulift.injective.comm_group _ rfl (λ _ _, rfl) (λ _, rfl)
  (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance group_with_zero [group_with_zero α] : group_with_zero (ulift α) :=
equiv.ulift.injective.group_with_zero _ rfl rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl)
  (λ _ _, rfl)

instance comm_group_with_zero [comm_group_with_zero α] : comm_group_with_zero (ulift α) :=
equiv.ulift.injective.comm_group_with_zero _ rfl rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)
  (λ _ _, rfl) (λ _ _, rfl)

@[to_additive add_left_cancel_semigroup]
instance left_cancel_semigroup [left_cancel_semigroup α] :
  left_cancel_semigroup (ulift α) :=
equiv.ulift.injective.left_cancel_semigroup _ (λ _ _, rfl)

@[to_additive add_right_cancel_semigroup]
instance right_cancel_semigroup [right_cancel_semigroup α] :
  right_cancel_semigroup (ulift α) :=
equiv.ulift.injective.right_cancel_semigroup _ (λ _ _, rfl)

@[to_additive add_left_cancel_monoid]
instance left_cancel_monoid [left_cancel_monoid α] :
  left_cancel_monoid (ulift α) :=
equiv.ulift.injective.left_cancel_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)

@[to_additive add_right_cancel_monoid]
instance right_cancel_monoid [right_cancel_monoid α] :
  right_cancel_monoid (ulift α) :=
equiv.ulift.injective.right_cancel_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)

@[to_additive add_cancel_monoid]
instance cancel_monoid [cancel_monoid α] :
  cancel_monoid (ulift α) :=
equiv.ulift.injective.cancel_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)

@[to_additive add_cancel_monoid]
instance cancel_comm_monoid [cancel_comm_monoid α] :
  cancel_comm_monoid (ulift α) :=
equiv.ulift.injective.cancel_comm_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)

instance nontrivial [nontrivial α] : nontrivial (ulift α) :=
equiv.ulift.symm.injective.nontrivial

-- TODO we don't do `ordered_cancel_comm_monoid` or `ordered_comm_group`
-- We'd need to add instances for `ulift` in `order.basic`.

end ulift
