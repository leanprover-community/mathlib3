/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.group.with_one.defs
import algebra.order.monoid.canonical.defs

/-!
# Adjoining a zero element to an ordered monoid.
-/

set_option old_structure_cmd true

open function

universe u
variables {α : Type u}

/-- Typeclass for expressing that the `0` of a type is less or equal to its `1`. -/
class zero_le_one_class (α : Type*) [has_zero α] [has_one α] [has_le α] :=
(zero_le_one : (0 : α) ≤ 1)

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

/-- `zero_le_one` with the type argument implicit. -/
@[simp] lemma zero_le_one [has_zero α] [has_one α] [has_le α] [zero_le_one_class α] : (0 : α) ≤ 1 :=
zero_le_one_class.zero_le_one

/-- `zero_le_one` with the type argument explicit. -/
lemma zero_le_one' (α) [has_zero α] [has_one α] [has_le α] [zero_le_one_class α] : (0 : α) ≤ 1 :=
zero_le_one

lemma zero_le_two [preorder α] [has_one α] [add_zero_class α] [zero_le_one_class α]
  [covariant_class α α (+) (≤)] : (0 : α) ≤ 2 :=
add_nonneg zero_le_one zero_le_one

lemma zero_le_three [preorder α] [has_one α] [add_zero_class α] [zero_le_one_class α]
  [covariant_class α α (+) (≤)] : (0 : α) ≤ 3 :=
add_nonneg zero_le_two zero_le_one

lemma zero_le_four [preorder α] [has_one α] [add_zero_class α] [zero_le_one_class α]
  [covariant_class α α (+) (≤)] : (0 : α) ≤ 4 :=
add_nonneg zero_le_two zero_le_two

lemma one_le_two [has_le α] [has_one α] [add_zero_class α] [zero_le_one_class α]
  [covariant_class α α (+) (≤)] : (1 : α) ≤ 2 :=
calc 1 = 1 + 0 : (add_zero 1).symm
   ... ≤ 1 + 1 : add_le_add_left zero_le_one _

lemma one_le_two' [has_le α] [has_one α] [add_zero_class α] [zero_le_one_class α]
  [covariant_class α α (swap (+)) (≤)] : (1 : α) ≤ 2 :=
calc 1 = 0 + 1 : (zero_add 1).symm
   ... ≤ 1 + 1 : add_le_add_right zero_le_one _

section
variables [has_zero α] [has_one α] [partial_order α] [zero_le_one_class α] [ne_zero (1 : α)]

/-- See `zero_lt_one'` for a version with the type explicit. -/
@[simp] lemma zero_lt_one : (0 : α) < 1 := zero_le_one.lt_of_ne (ne_zero.ne' 1)

variables (α)

/-- See `zero_lt_one` for a version with the type implicit. -/
lemma zero_lt_one' : (0 : α) < 1 := zero_lt_one

end

section
variables [has_one α] [add_zero_class α] [partial_order α] [zero_le_one_class α] [ne_zero (1 : α)]

section
variables [covariant_class α α (+) (≤)]

/-- See `zero_lt_two'` for a version with the type explicit. -/
@[simp] lemma zero_lt_two : (0 : α) < 2 := zero_lt_one.trans_le one_le_two
/-- See `zero_lt_three'` for a version with the type explicit. -/
@[simp] lemma zero_lt_three : (0 : α) < 3 := lt_add_of_lt_of_nonneg zero_lt_two zero_le_one
/-- See `zero_lt_four'` for a version with the type explicit. -/
@[simp] lemma zero_lt_four : (0 : α) < 4 := lt_add_of_lt_of_nonneg zero_lt_two zero_le_two

variables (α)

/-- See `zero_lt_two` for a version with the type implicit. -/
lemma zero_lt_two' : (0 : α) < 2 := zero_lt_two
/-- See `zero_lt_three` for a version with the type implicit. -/
lemma zero_lt_three' : (0 : α) < 3 := zero_lt_three
/-- See `zero_lt_four` for a version with the type implicit. -/
lemma zero_lt_four' : (0 : α) < 4 := zero_lt_four

instance zero_le_one_class.ne_zero.two : ne_zero (2 : α) := ⟨zero_lt_two.ne'⟩
instance zero_le_one_class.ne_zero.three : ne_zero (3 : α) := ⟨zero_lt_three.ne'⟩
instance zero_le_one_class.ne_zero.four : ne_zero (4 : α) := ⟨zero_lt_four.ne'⟩

end

lemma lt_add_one [covariant_class α α (+) (<)] (a : α) : a < a + 1 :=
lt_add_of_pos_right _ zero_lt_one

lemma lt_one_add [covariant_class α α (swap (+)) (<)] (a : α) : a < 1 + a :=
lt_add_of_pos_left _ zero_lt_one

lemma one_lt_two [covariant_class α α (+) (<)] : (1 : α) < 2 := lt_add_one _

end

alias zero_lt_one ← one_pos
alias zero_lt_two ← two_pos
alias zero_lt_three ← three_pos
alias zero_lt_four ← four_pos

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
