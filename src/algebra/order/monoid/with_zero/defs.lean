/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.group.with_one.defs
import algebra.order.monoid.canonical.defs
import algebra.order.zero_le_one

/-!
# Adjoining a zero element to an ordered monoid.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

set_option old_structure_cmd true

universe u
variables {α : Type u}

/-- A linearly ordered commutative monoid with a zero element. -/
class linear_ordered_comm_monoid_with_zero (α : Type*)
  extends linear_ordered_comm_monoid α, comm_monoid_with_zero α :=
(zero_le_one : (0 : α) ≤ 1)

@[priority 100]
instance linear_ordered_comm_monoid_with_zero.to_zero_le_one_class
  [linear_ordered_comm_monoid_with_zero α] : zero_le_one_class α :=
{ ..‹linear_ordered_comm_monoid_with_zero α› }

@[priority 100]
instance canonically_ordered_add_monoid.to_zero_le_one_class [canonically_ordered_add_monoid α]
  [has_one α] : zero_le_one_class α :=
⟨zero_le 1⟩

namespace with_zero

local attribute [semireducible] with_zero

instance [preorder α] : preorder (with_zero α) := with_bot.preorder

instance [partial_order α] : partial_order (with_zero α) := with_bot.partial_order

instance [preorder α] : order_bot (with_zero α) := with_bot.order_bot

lemma zero_le [preorder α] (a : with_zero α) : 0 ≤ a := bot_le

lemma zero_lt_coe [preorder α] (a : α) : (0 : with_zero α) < a := with_bot.bot_lt_coe a

lemma zero_eq_bot [preorder α] : (0 : with_zero α) = ⊥ := rfl

@[simp, norm_cast] lemma coe_lt_coe [preorder α] {a b : α} : (a : with_zero α) < b ↔ a < b :=
with_bot.coe_lt_coe

@[simp, norm_cast] lemma coe_le_coe [preorder α] {a b : α} : (a : with_zero α) ≤ b ↔ a ≤ b :=
with_bot.coe_le_coe

instance [lattice α] : lattice (with_zero α) := with_bot.lattice

instance [linear_order α] : linear_order (with_zero α) := with_bot.linear_order

instance covariant_class_mul_le {α : Type u} [has_mul α] [preorder α]
  [covariant_class α α (*) (≤)] :
  covariant_class (with_zero α) (with_zero α) (*) (≤) :=
begin
  refine ⟨λ a b c hbc, _⟩,
  induction a using with_zero.rec_zero_coe, { exact zero_le _ },
  induction b using with_zero.rec_zero_coe, { exact zero_le _ },
  rcases with_bot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩,
  rw [← coe_mul, ← coe_mul, coe_le_coe],
  exact mul_le_mul_left' hbc' a
end

@[simp] lemma le_max_iff [linear_order α] {a b c : α} :
  (a : with_zero α) ≤ max b c ↔ a ≤ max b c :=
by simp only [with_zero.coe_le_coe, le_max_iff]

@[simp] lemma min_le_iff [linear_order α] {a b c : α} :
   min (a : with_zero α) b ≤ c ↔ min a b ≤ c :=
by simp only [with_zero.coe_le_coe, min_le_iff]

instance [ordered_comm_monoid α] : ordered_comm_monoid (with_zero α) :=
{ mul_le_mul_left := λ _ _, mul_le_mul_left',
  ..with_zero.comm_monoid_with_zero,
  ..with_zero.partial_order }

protected lemma covariant_class_add_le [add_zero_class α] [preorder α]
  [covariant_class α α (+) (≤)] (h : ∀ a : α, 0 ≤ a) :
  covariant_class (with_zero α) (with_zero α) (+) (≤) :=
begin
  refine ⟨λ a b c hbc, _⟩,
  induction a using with_zero.rec_zero_coe,
  { rwa [zero_add, zero_add] },
  induction b using with_zero.rec_zero_coe,
  { rw [add_zero],
    induction c using with_zero.rec_zero_coe,
    { rw [add_zero], exact le_rfl },
    { rw [← coe_add, coe_le_coe],
      exact le_add_of_nonneg_right (h _) } },
  { rcases with_bot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩,
    rw [← coe_add, ← coe_add, coe_le_coe],
    exact add_le_add_left hbc' a }
end

/-
Note 1 : the below is not an instance because it requires `zero_le`. It seems
like a rather pathological definition because α already has a zero.
Note 2 : there is no multiplicative analogue because it does not seem necessary.
Mathematicians might be more likely to use the order-dual version, where all
elements are ≤ 1 and then 1 is the top element.
-/

/--
If `0` is the least element in `α`, then `with_zero α` is an `ordered_add_comm_monoid`.
See note [reducible non-instances].
-/
@[reducible] protected def ordered_add_comm_monoid [ordered_add_comm_monoid α]
  (zero_le : ∀ a : α, 0 ≤ a) : ordered_add_comm_monoid (with_zero α) :=
{ add_le_add_left := @add_le_add_left _ _ _ (with_zero.covariant_class_add_le zero_le),
  ..with_zero.partial_order,
  ..with_zero.add_comm_monoid, .. }

end with_zero

section canonically_ordered_monoid

instance with_zero.has_exists_add_of_le {α} [has_add α] [preorder α] [has_exists_add_of_le α] :
  has_exists_add_of_le (with_zero α) :=
⟨λ a b, begin
  apply with_zero.cases_on a,
  { exact λ _, ⟨b, (zero_add b).symm⟩ },
  apply with_zero.cases_on b,
  { exact λ b' h, (with_bot.not_coe_le_bot _ h).elim },
  rintro a' b' h,
  obtain ⟨c, rfl⟩ := exists_add_of_le (with_zero.coe_le_coe.1 h),
  exact ⟨c, rfl⟩,
end⟩

-- This instance looks absurd: a monoid already has a zero
/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
instance with_zero.canonically_ordered_add_monoid {α : Type u} [canonically_ordered_add_monoid α] :
  canonically_ordered_add_monoid (with_zero α) :=
{ le_self_add := λ a b, begin
    apply with_zero.cases_on a,
    { exact bot_le },
    apply with_zero.cases_on b,
    { exact λ b', le_rfl },
    { exact λ a' b', with_zero.coe_le_coe.2 le_self_add }
  end,
  .. with_zero.order_bot,
  .. with_zero.ordered_add_comm_monoid zero_le, ..with_zero.has_exists_add_of_le }

end canonically_ordered_monoid

section canonically_linear_ordered_monoid

instance with_zero.canonically_linear_ordered_add_monoid
  (α : Type*) [canonically_linear_ordered_add_monoid α] :
    canonically_linear_ordered_add_monoid (with_zero α) :=
{ .. with_zero.canonically_ordered_add_monoid,
  .. with_zero.linear_order }

end canonically_linear_ordered_monoid
