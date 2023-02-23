/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.group.ulift
import algebra.field.defs
import algebra.ring.equiv

/-!
# `ulift` instances for ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for ring, semiring and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ulift.ring_equiv : ulift R ≃+* R`.
-/

universes u v
variables {α : Type u} {x y : ulift.{v} α}

namespace ulift

instance mul_zero_class [mul_zero_class α] : mul_zero_class (ulift α) :=
by refine_struct { zero := (0 : ulift α), mul := (*), .. }; tactic.pi_instance_derive_field

instance distrib [distrib α] : distrib (ulift α) :=
by refine_struct { add := (+), mul := (*), .. }; tactic.pi_instance_derive_field

instance non_unital_non_assoc_semiring [non_unital_non_assoc_semiring α] :
  non_unital_non_assoc_semiring (ulift α) :=
by refine_struct { zero := (0 : ulift α), add := (+), mul := (*),
  nsmul := add_monoid.nsmul, };
tactic.pi_instance_derive_field

instance non_assoc_semiring [non_assoc_semiring α] : non_assoc_semiring (ulift α) :=
by refine_struct { zero := (0 : ulift α), one := 1, add := (+), mul := (*),
  nsmul := add_monoid.nsmul, .. ulift.add_monoid_with_one };
tactic.pi_instance_derive_field

instance non_unital_semiring [non_unital_semiring α] : non_unital_semiring (ulift α) :=
by refine_struct { zero := (0 : ulift α), add := (+), mul := (*),
  nsmul := add_monoid.nsmul, };
tactic.pi_instance_derive_field

instance semiring [semiring α] : semiring (ulift α) :=
by refine_struct { zero := (0 : ulift α), one := 1, add := (+), mul := (*),
  nsmul := add_monoid.nsmul, npow := monoid.npow, .. ulift.add_monoid_with_one };
tactic.pi_instance_derive_field

/--
The ring equivalence between `ulift α` and `α`.
-/
def ring_equiv [non_unital_non_assoc_semiring α] : ulift α ≃+* α :=
{ to_fun := ulift.down,
  inv_fun := ulift.up,
  map_mul' := λ x y, rfl,
  map_add' := λ x y, rfl,
  left_inv := by tidy,
  right_inv := by tidy, }

instance non_unital_comm_semiring [non_unital_comm_semiring α] :
  non_unital_comm_semiring (ulift α) :=
by refine_struct { zero := (0 : ulift α), add := (+), mul := (*), nsmul := add_monoid.nsmul };
tactic.pi_instance_derive_field

instance comm_semiring [comm_semiring α] : comm_semiring (ulift α) :=
by refine_struct { zero := (0 : ulift α), one := 1, add := (+), mul := (*),
  nsmul := add_monoid.nsmul, npow := monoid.npow, .. ulift.semiring };
tactic.pi_instance_derive_field

instance non_unital_non_assoc_ring [non_unital_non_assoc_ring α] :
  non_unital_non_assoc_ring (ulift α) :=
by refine_struct { zero := (0 : ulift α), add := (+), mul := (*), sub := has_sub.sub,
  neg := has_neg.neg, nsmul := add_monoid.nsmul, zsmul := sub_neg_monoid.zsmul };
tactic.pi_instance_derive_field

instance non_unital_ring [non_unital_ring α] :
  non_unital_ring (ulift α) :=
by refine_struct { zero := (0 : ulift α), add := (+), mul := (*), sub := has_sub.sub,
  neg := has_neg.neg, nsmul := add_monoid.nsmul, zsmul := sub_neg_monoid.zsmul };
tactic.pi_instance_derive_field

instance non_assoc_ring [non_assoc_ring α] :
  non_assoc_ring (ulift α) :=
by refine_struct { zero := (0 : ulift α), one := 1, add := (+), mul := (*), sub := has_sub.sub,
  neg := has_neg.neg, nsmul := add_monoid.nsmul, zsmul := sub_neg_monoid.zsmul,
  .. ulift.add_group_with_one };
tactic.pi_instance_derive_field

instance ring [ring α] : ring (ulift α) :=
by refine_struct { zero := (0 : ulift α), one := 1, add := (+), mul := (*), sub := has_sub.sub,
  neg := has_neg.neg, nsmul := add_monoid.nsmul, npow := monoid.npow,
  zsmul := sub_neg_monoid.zsmul, .. ulift.semiring, .. ulift.add_group_with_one };
tactic.pi_instance_derive_field

instance non_unital_comm_ring [non_unital_comm_ring α] : non_unital_comm_ring (ulift α) :=
by refine_struct { zero := (0 : ulift α), add := (+), mul := (*), sub := has_sub.sub,
  neg := has_neg.neg, nsmul := add_monoid.nsmul, zsmul := sub_neg_monoid.zsmul };
tactic.pi_instance_derive_field

instance comm_ring [comm_ring α] : comm_ring (ulift α) :=
by refine_struct { .. ulift.ring };
tactic.pi_instance_derive_field

instance [has_rat_cast α] : has_rat_cast (ulift α) :=
⟨λ a, ulift.up (coe a)⟩

@[simp] lemma rat_cast_down [has_rat_cast α] (n : ℚ) : ulift.down (n : ulift α) = n :=
rfl

instance field [field α] : field (ulift α) :=
begin
  have of_rat_mk : ∀ a b h1 h2, ((⟨a, b, h1, h2⟩ : ℚ) : ulift α) = ↑a * (↑b)⁻¹,
  { intros a b h1 h2,
    ext,
    rw [rat_cast_down, mul_down, inv_down, nat_cast_down, int_cast_down],
    exact field.rat_cast_mk a b h1 h2 },
  refine_struct { zero := (0 : ulift α), inv := has_inv.inv, div := has_div.div,
  zpow := λ n a, ulift.up (a.down ^ n), rat_cast := coe, rat_cast_mk := of_rat_mk, qsmul := (•),
  .. @ulift.nontrivial α _, .. ulift.comm_ring }; tactic.pi_instance_derive_field,
  -- `mul_inv_cancel` requires special attention: it leaves the goal `∀ {a}, a ≠ 0 → a * a⁻¹ = 1`.
  cases a,
  tauto
end

end ulift
