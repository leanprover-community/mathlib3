/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import algebra.order.ring.defs
import algebra.ring.pi
import tactic.positivity

/-!
# Pi instances for ordered groups and monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for ordered group, monoid, and related structures on Pi types.
-/

universes u v w
variables {ι α β : Type*}
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

namespace pi

/-- The product of a family of ordered commutative monoids is an ordered commutative monoid. -/
@[to_additive "The product of a family of ordered additive commutative monoids is
  an ordered additive commutative monoid."]
instance ordered_comm_monoid {ι : Type*} {Z : ι → Type*} [∀ i, ordered_comm_monoid (Z i)] :
  ordered_comm_monoid (Π i, Z i) :=
{ mul_le_mul_left := λ f g w h i, mul_le_mul_left' (w i) _,
  ..pi.partial_order,
  ..pi.comm_monoid, }

@[to_additive] instance {ι : Type*} {α : ι → Type*} [Π i, has_le (α i)] [Π i, has_mul (α i)]
  [Π i, has_exists_mul_of_le (α i)] :
  has_exists_mul_of_le (Π i, α i) :=
⟨λ a b h, ⟨λ i, (exists_mul_of_le $ h i).some, funext $ λ i, (exists_mul_of_le $ h i).some_spec⟩⟩

/-- The product of a family of canonically ordered monoids is a canonically ordered monoid. -/
@[to_additive "The product of a family of canonically ordered additive monoids is
  a canonically ordered additive monoid."]
instance {ι : Type*} {Z : ι → Type*} [∀ i, canonically_ordered_monoid (Z i)] :
  canonically_ordered_monoid (Π i, Z i) :=
{ le_self_mul := λ f g i, le_self_mul,
  ..pi.order_bot, ..pi.ordered_comm_monoid, ..pi.has_exists_mul_of_le }

@[to_additive]
instance ordered_cancel_comm_monoid [∀ i, ordered_cancel_comm_monoid $ f i] :
  ordered_cancel_comm_monoid (Π i : I, f i) :=
by refine_struct { mul := (*), one := (1 : Π i, f i), le := (≤), lt := (<),
  npow := monoid.npow, .. pi.partial_order, .. pi.monoid };
  tactic.pi_instance_derive_field

@[to_additive]
instance ordered_comm_group [∀ i, ordered_comm_group $ f i] :
  ordered_comm_group (Π i : I, f i) :=
{ mul := (*), one := (1 : Π i, f i), le := (≤), lt := (<),
  npow := monoid.npow,
  ..pi.comm_group,
  ..pi.ordered_comm_monoid, }

instance [Π i, ordered_semiring (f i)] : ordered_semiring (Π i, f i) :=
{ add_le_add_left := λ a b hab c i, add_le_add_left (hab _) _,
  zero_le_one := λ _, zero_le_one,
  mul_le_mul_of_nonneg_left := λ a b c hab hc i, mul_le_mul_of_nonneg_left (hab _) $ hc _,
  mul_le_mul_of_nonneg_right := λ a b c hab hc i, mul_le_mul_of_nonneg_right (hab _) $ hc _,
    ..pi.semiring, ..pi.partial_order }

instance [Π i, ordered_comm_semiring (f i)] : ordered_comm_semiring (Π i, f i) :=
{ ..pi.comm_semiring, ..pi.ordered_semiring }

instance [Π i, ordered_ring (f i)] : ordered_ring (Π i, f i) :=
{ mul_nonneg := λ a b ha hb i, mul_nonneg (ha _) (hb _),
    ..pi.ring, ..pi.ordered_semiring }

instance [Π i, ordered_comm_ring (f i)] : ordered_comm_ring (Π i, f i) :=
{ ..pi.comm_ring, ..pi.ordered_ring }

end pi

namespace function
variables (β) [has_one α] [preorder α] {a : α}

@[to_additive const_nonneg_of_nonneg]
lemma one_le_const_of_one_le (ha : 1 ≤ a) : 1 ≤ const β a := λ _, ha

@[to_additive] lemma const_le_one_of_le_one (ha : a ≤ 1) : const β a ≤ 1 := λ _, ha

variables {β} [nonempty β]

@[simp, to_additive const_nonneg]
lemma one_le_const : 1 ≤ const β a ↔ 1 ≤ a := @const_le_const _ _ _ _ 1 _
@[simp, to_additive const_pos]
lemma one_lt_const : 1 < const β a ↔ 1 < a := @const_lt_const _ _ _ _ 1 a
@[simp, to_additive] lemma const_le_one : const β a ≤ 1 ↔ a ≤ 1 := @const_le_const _ _ _ _ _ 1
@[simp, to_additive] lemma const_lt_one : const β a < 1 ↔ a < 1 := @const_lt_const _ _ _ _ _ 1

end function

namespace tactic
open function positivity
variables (ι) [has_zero α] {a : α}

private lemma function_const_nonneg_of_pos [preorder α] (ha : 0 < a) : 0 ≤ const ι a :=
const_nonneg_of_nonneg _ ha.le

variables [nonempty ι]

private lemma function_const_ne_zero : a ≠ 0 → const ι a ≠ 0 := const_ne_zero.2
private lemma function_const_pos [preorder α] : 0 < a → 0 < const ι a := const_pos.2

/-- Extension for the `positivity` tactic: `function.const` is positive/nonnegative/nonzero if its
input is. -/
@[positivity]
meta def positivity_const : expr → tactic strictness
| `(function.const %%ι %%a) := do
    strict_a ← core a,
    match strict_a with
    | positive p := positive <$> to_expr ``(function_const_pos %%ι %%p)
        <|> nonnegative <$> to_expr ``(function_const_nonneg_of_pos %%ι %%p)
    | nonnegative p := nonnegative <$> to_expr ``(const_nonneg_of_nonneg %%ι %%p)
    | nonzero p := nonzero <$> to_expr ``(function_const_ne_zero %%ι %%p)
    end
| e := pp e >>= fail ∘ format.bracket "The expression `" "` is not of the form `function.const ι a`"

end tactic
