/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import order.hom.basic
import algebra.order.sub.defs
import algebra.order.monoid.cancel.defs

/-!
# Ordered groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file develops the basics of ordered groups.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/

set_option old_structure_cmd true
open function

universe u
variable {α : Type u}

/-- An ordered additive commutative group is an additive commutative group
with a partial order in which addition is strictly monotone. -/
@[protect_proj, ancestor add_comm_group partial_order]
class ordered_add_comm_group (α : Type u) extends add_comm_group α, partial_order α :=
(add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)

/-- An ordered commutative group is an commutative group
with a partial order in which multiplication is strictly monotone. -/
@[protect_proj, ancestor comm_group partial_order]
class ordered_comm_group (α : Type u) extends comm_group α, partial_order α :=
(mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
attribute [to_additive] ordered_comm_group

@[to_additive]
instance ordered_comm_group.to_covariant_class_left_le (α : Type u) [ordered_comm_group α] :
  covariant_class α α (*) (≤) :=
{ elim := λ a b c bc, ordered_comm_group.mul_le_mul_left b c bc a }

@[priority 100, to_additive] -- See note [lower instance priority]
instance ordered_comm_group.to_ordered_cancel_comm_monoid [ordered_comm_group α] :
  ordered_cancel_comm_monoid α :=
{ le_of_mul_le_mul_left := λ a b c, le_of_mul_le_mul_left',
  ..‹ordered_comm_group α› }

example (α : Type u) [ordered_add_comm_group α] : covariant_class α α (swap (+)) (<) :=
add_right_cancel_semigroup.covariant_swap_add_lt_of_covariant_swap_add_le α

/-- A choice-free shortcut instance. -/
@[to_additive "A choice-free shortcut instance."]
instance ordered_comm_group.to_contravariant_class_left_le (α : Type u) [ordered_comm_group α] :
  contravariant_class α α (*) (≤) :=
{ elim := λ a b c bc, by simpa using mul_le_mul_left' bc a⁻¹, }

/-- A choice-free shortcut instance. -/
@[to_additive "A choice-free shortcut instance."]
instance ordered_comm_group.to_contravariant_class_right_le (α : Type u) [ordered_comm_group α] :
  contravariant_class α α (swap (*)) (≤) :=
{ elim := λ a b c bc, by simpa using mul_le_mul_right' bc a⁻¹, }

section group
variables [group α]

section typeclasses_left_le
variables [has_le α] [covariant_class α α (*) (≤)] {a b c d : α}

/--  Uses `left` co(ntra)variant. -/
@[simp, to_additive left.neg_nonpos_iff "Uses `left` co(ntra)variant."]
lemma left.inv_le_one_iff :
  a⁻¹ ≤ 1 ↔ 1 ≤ a :=
by { rw [← mul_le_mul_iff_left a], simp }

/--  Uses `left` co(ntra)variant. -/
@[simp, to_additive left.nonneg_neg_iff "Uses `left` co(ntra)variant."]
lemma left.one_le_inv_iff :
  1 ≤ a⁻¹ ↔ a ≤ 1 :=
by { rw [← mul_le_mul_iff_left a], simp }

@[simp, to_additive]
lemma le_inv_mul_iff_mul_le : b ≤ a⁻¹ * c ↔ a * b ≤ c :=
by { rw ← mul_le_mul_iff_left a, simp }

@[simp, to_additive]
lemma inv_mul_le_iff_le_mul : b⁻¹ * a ≤ c ↔ a ≤ b * c :=
by rw [← mul_le_mul_iff_left b, mul_inv_cancel_left]

@[to_additive neg_le_iff_add_nonneg']
lemma inv_le_iff_one_le_mul' : a⁻¹ ≤ b ↔ 1 ≤ a * b :=
(mul_le_mul_iff_left a).symm.trans $ by rw mul_inv_self

@[to_additive]
lemma le_inv_iff_mul_le_one_left : a ≤ b⁻¹ ↔ b * a ≤ 1 :=
(mul_le_mul_iff_left b).symm.trans $ by rw mul_inv_self

@[to_additive]
lemma le_inv_mul_iff_le : 1 ≤ b⁻¹ * a ↔ b ≤ a :=
by rw [← mul_le_mul_iff_left b, mul_one, mul_inv_cancel_left]

@[to_additive]
lemma inv_mul_le_one_iff : a⁻¹ * b ≤ 1 ↔ b ≤ a :=
trans (inv_mul_le_iff_le_mul) $ by rw mul_one

end typeclasses_left_le

section typeclasses_left_lt
variables [has_lt α] [covariant_class α α (*) (<)] {a b c : α}

/--  Uses `left` co(ntra)variant. -/
@[simp, to_additive left.neg_pos_iff "Uses `left` co(ntra)variant."]
lemma left.one_lt_inv_iff :
  1 < a⁻¹ ↔ a < 1 :=
by rw [← mul_lt_mul_iff_left a, mul_inv_self, mul_one]

/--  Uses `left` co(ntra)variant. -/
@[simp, to_additive left.neg_neg_iff "Uses `left` co(ntra)variant."]
lemma left.inv_lt_one_iff :
  a⁻¹ < 1 ↔ 1 < a :=
by rw [← mul_lt_mul_iff_left a, mul_inv_self, mul_one]

@[simp, to_additive]
lemma lt_inv_mul_iff_mul_lt : b < a⁻¹ * c ↔ a * b < c :=
by { rw [← mul_lt_mul_iff_left a], simp }

@[simp, to_additive]
lemma inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c :=
by rw [← mul_lt_mul_iff_left b, mul_inv_cancel_left]

@[to_additive]
lemma inv_lt_iff_one_lt_mul' : a⁻¹ < b ↔ 1 < a * b :=
(mul_lt_mul_iff_left a).symm.trans $ by rw mul_inv_self

@[to_additive]
lemma lt_inv_iff_mul_lt_one' : a < b⁻¹ ↔ b * a < 1 :=
(mul_lt_mul_iff_left b).symm.trans $ by rw mul_inv_self

@[to_additive]
lemma lt_inv_mul_iff_lt : 1 < b⁻¹ * a ↔ b < a :=
by rw [← mul_lt_mul_iff_left b, mul_one, mul_inv_cancel_left]

@[to_additive]
lemma inv_mul_lt_one_iff : a⁻¹ * b < 1 ↔ b < a :=
trans (inv_mul_lt_iff_lt_mul) $ by rw mul_one

end typeclasses_left_lt

section typeclasses_right_le
variables [has_le α] [covariant_class α α (swap (*)) (≤)] {a b c : α}

/--  Uses `right` co(ntra)variant. -/
@[simp, to_additive right.neg_nonpos_iff "Uses `right` co(ntra)variant."]
lemma right.inv_le_one_iff :
  a⁻¹ ≤ 1 ↔ 1 ≤ a :=
by { rw [← mul_le_mul_iff_right a], simp }

/--  Uses `right` co(ntra)variant. -/
@[simp, to_additive right.nonneg_neg_iff "Uses `right` co(ntra)variant."]
lemma right.one_le_inv_iff :
  1 ≤ a⁻¹ ↔ a ≤ 1 :=
by { rw [← mul_le_mul_iff_right a], simp }

@[to_additive neg_le_iff_add_nonneg]
lemma inv_le_iff_one_le_mul : a⁻¹ ≤ b ↔ 1 ≤ b * a :=
(mul_le_mul_iff_right a).symm.trans $ by rw inv_mul_self

@[to_additive]
lemma le_inv_iff_mul_le_one_right : a ≤ b⁻¹ ↔ a * b ≤ 1 :=
(mul_le_mul_iff_right b).symm.trans $ by rw inv_mul_self

@[simp, to_additive]
lemma mul_inv_le_iff_le_mul : a * b⁻¹ ≤ c ↔ a ≤ c * b :=
(mul_le_mul_iff_right b).symm.trans $ by rw inv_mul_cancel_right

@[simp, to_additive]
lemma le_mul_inv_iff_mul_le : c ≤ a * b⁻¹ ↔ c * b ≤ a :=
(mul_le_mul_iff_right b).symm.trans $ by rw inv_mul_cancel_right

@[simp, to_additive]
lemma mul_inv_le_one_iff_le : a * b⁻¹ ≤ 1 ↔ a ≤ b :=
mul_inv_le_iff_le_mul.trans $ by rw one_mul

@[to_additive]
lemma le_mul_inv_iff_le : 1 ≤ a * b⁻¹ ↔ b ≤ a :=
by rw [← mul_le_mul_iff_right b, one_mul, inv_mul_cancel_right]

@[to_additive]
lemma mul_inv_le_one_iff : b * a⁻¹ ≤ 1 ↔ b ≤ a :=
trans (mul_inv_le_iff_le_mul) $ by rw one_mul

end typeclasses_right_le

section typeclasses_right_lt
variables [has_lt α] [covariant_class α α (swap (*)) (<)] {a b c : α}

/-- Uses `right` co(ntra)variant. -/
@[simp, to_additive right.neg_neg_iff "Uses `right` co(ntra)variant."]
lemma right.inv_lt_one_iff :
  a⁻¹ < 1 ↔ 1 < a :=
by rw [← mul_lt_mul_iff_right a, inv_mul_self, one_mul]

/-- Uses `right` co(ntra)variant. -/
@[simp, to_additive right.neg_pos_iff "Uses `right` co(ntra)variant."]
lemma right.one_lt_inv_iff :
  1 < a⁻¹ ↔ a < 1 :=
by rw [← mul_lt_mul_iff_right a, inv_mul_self, one_mul]

@[to_additive]
lemma inv_lt_iff_one_lt_mul : a⁻¹ < b ↔ 1 < b * a :=
(mul_lt_mul_iff_right a).symm.trans $ by rw inv_mul_self

@[to_additive]
lemma lt_inv_iff_mul_lt_one : a < b⁻¹ ↔ a * b < 1 :=
(mul_lt_mul_iff_right b).symm.trans $ by rw inv_mul_self

@[simp, to_additive]
lemma mul_inv_lt_iff_lt_mul : a * b⁻¹ < c ↔ a < c * b :=
by rw [← mul_lt_mul_iff_right b, inv_mul_cancel_right]

@[simp, to_additive]
lemma lt_mul_inv_iff_mul_lt : c < a * b⁻¹ ↔ c * b < a :=
(mul_lt_mul_iff_right b).symm.trans $ by rw inv_mul_cancel_right

@[simp, to_additive]
lemma inv_mul_lt_one_iff_lt : a * b⁻¹ < 1 ↔ a < b :=
by rw [← mul_lt_mul_iff_right b, inv_mul_cancel_right, one_mul]

@[to_additive]
lemma lt_mul_inv_iff_lt : 1 < a * b⁻¹ ↔ b < a :=
by rw [← mul_lt_mul_iff_right b, one_mul, inv_mul_cancel_right]

@[to_additive]
lemma mul_inv_lt_one_iff : b * a⁻¹ < 1 ↔ b < a :=
trans (mul_inv_lt_iff_lt_mul) $ by rw one_mul

end typeclasses_right_lt

section typeclasses_left_right_le
variables [has_le α] [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)]
  {a b c d : α}

@[simp, to_additive]
lemma inv_le_inv_iff : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
by { rw [← mul_le_mul_iff_left a, ← mul_le_mul_iff_right b], simp }

alias neg_le_neg_iff ↔ le_of_neg_le_neg _

@[to_additive]
lemma mul_inv_le_inv_mul_iff : a * b⁻¹ ≤ d⁻¹ * c ↔ d * a ≤ c * b :=
by rw [← mul_le_mul_iff_left d, ← mul_le_mul_iff_right b, mul_inv_cancel_left, mul_assoc,
    inv_mul_cancel_right]

@[simp, to_additive] lemma div_le_self_iff (a : α) {b : α} : a / b ≤ a ↔ 1 ≤ b :=
by simp [div_eq_mul_inv]

@[simp, to_additive] lemma le_div_self_iff (a : α) {b : α} : a ≤ a / b ↔ b ≤ 1 :=
by simp [div_eq_mul_inv]

alias sub_le_self_iff ↔ _ sub_le_self

end typeclasses_left_right_le

section typeclasses_left_right_lt
variables [has_lt α] [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (<)]
  {a b c d : α}

@[simp, to_additive]
lemma inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a :=
by { rw [← mul_lt_mul_iff_left a, ← mul_lt_mul_iff_right b], simp }

@[to_additive neg_lt]
lemma inv_lt' : a⁻¹ < b ↔ b⁻¹ < a :=
by rw [← inv_lt_inv_iff, inv_inv]

@[to_additive lt_neg]
lemma lt_inv' : a < b⁻¹ ↔ b < a⁻¹ :=
by rw [← inv_lt_inv_iff, inv_inv]

alias lt_inv' ↔ lt_inv_of_lt_inv _
attribute [to_additive] lt_inv_of_lt_inv

alias inv_lt' ↔ inv_lt_of_inv_lt' _
attribute [to_additive neg_lt_of_neg_lt] inv_lt_of_inv_lt'

@[to_additive]
lemma mul_inv_lt_inv_mul_iff : a * b⁻¹ < d⁻¹ * c ↔ d * a < c * b :=
by rw [← mul_lt_mul_iff_left d, ← mul_lt_mul_iff_right b, mul_inv_cancel_left, mul_assoc,
    inv_mul_cancel_right]

@[simp, to_additive] lemma div_lt_self_iff (a : α) {b : α} : a / b < a ↔ 1 < b :=
by simp [div_eq_mul_inv]

alias sub_lt_self_iff ↔ _ sub_lt_self

end typeclasses_left_right_lt

section pre_order
variable [preorder α]

section left_le
variables [covariant_class α α (*) (≤)] {a : α}

@[to_additive]
lemma left.inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a :=
le_trans (left.inv_le_one_iff.mpr h) h

alias left.neg_le_self ← neg_le_self

@[to_additive]
lemma left.self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ :=
le_trans h (left.one_le_inv_iff.mpr h)

end left_le

section left_lt
variables [covariant_class α α (*) (<)] {a : α}

@[to_additive]
lemma left.inv_lt_self (h : 1 < a) : a⁻¹ < a :=
(left.inv_lt_one_iff.mpr h).trans h

alias left.neg_lt_self ← neg_lt_self

@[to_additive]
lemma left.self_lt_inv (h : a < 1) : a < a⁻¹ :=
lt_trans h (left.one_lt_inv_iff.mpr h)

end left_lt

section right_le
variables [covariant_class α α (swap (*)) (≤)] {a : α}

@[to_additive]
lemma right.inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a :=
le_trans (right.inv_le_one_iff.mpr h) h

@[to_additive]
lemma right.self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ :=
le_trans h (right.one_le_inv_iff.mpr h)

end right_le

section right_lt
variables [covariant_class α α (swap (*)) (<)] {a : α}

@[to_additive]
lemma right.inv_lt_self (h : 1 < a) : a⁻¹ < a :=
(right.inv_lt_one_iff.mpr h).trans h

@[to_additive]
lemma right.self_lt_inv (h : a < 1) : a < a⁻¹ :=
lt_trans h (right.one_lt_inv_iff.mpr h)

end right_lt

end pre_order

end group

section comm_group
variables [comm_group α]

section has_le
variables [has_le α] [covariant_class α α (*) (≤)] {a b c d : α}

@[to_additive]
lemma inv_mul_le_iff_le_mul' : c⁻¹ * a ≤ b ↔ a ≤ b * c :=
by rw [inv_mul_le_iff_le_mul, mul_comm]

@[simp, to_additive]
lemma mul_inv_le_iff_le_mul' : a * b⁻¹ ≤ c ↔ a ≤ b * c :=
by rw [← inv_mul_le_iff_le_mul, mul_comm]

@[to_additive add_neg_le_add_neg_iff]
lemma mul_inv_le_mul_inv_iff' : a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b :=
by rw [mul_comm c, mul_inv_le_inv_mul_iff, mul_comm]

end has_le

section has_lt
variables [has_lt α] [covariant_class α α (*) (<)] {a b c d : α}

@[to_additive]
lemma inv_mul_lt_iff_lt_mul' : c⁻¹ * a < b ↔ a < b * c :=
by rw [inv_mul_lt_iff_lt_mul, mul_comm]

@[simp, to_additive]
lemma mul_inv_lt_iff_le_mul' : a * b⁻¹ < c ↔ a < b * c :=
by rw [← inv_mul_lt_iff_lt_mul, mul_comm]

@[to_additive add_neg_lt_add_neg_iff]
lemma mul_inv_lt_mul_inv_iff' : a * b⁻¹ < c * d⁻¹ ↔ a * d < c * b :=
by rw [mul_comm c, mul_inv_lt_inv_mul_iff, mul_comm]

end has_lt

end comm_group

alias left.inv_le_one_iff ↔ one_le_of_inv_le_one _
attribute [to_additive] one_le_of_inv_le_one

alias left.one_le_inv_iff ↔ le_one_of_one_le_inv _
attribute [to_additive nonpos_of_neg_nonneg] le_one_of_one_le_inv

alias inv_lt_inv_iff ↔ lt_of_inv_lt_inv _
attribute [to_additive] lt_of_inv_lt_inv

alias left.inv_lt_one_iff ↔ one_lt_of_inv_lt_one _
attribute [to_additive] one_lt_of_inv_lt_one

alias left.inv_lt_one_iff ← inv_lt_one_iff_one_lt
attribute [to_additive] inv_lt_one_iff_one_lt

alias left.inv_lt_one_iff ← inv_lt_one'
attribute [to_additive neg_lt_zero] inv_lt_one'

alias left.one_lt_inv_iff ↔  inv_of_one_lt_inv _
attribute [to_additive neg_of_neg_pos] inv_of_one_lt_inv

alias left.one_lt_inv_iff ↔ _ one_lt_inv_of_inv
attribute [to_additive neg_pos_of_neg] one_lt_inv_of_inv

alias le_inv_mul_iff_mul_le ↔ mul_le_of_le_inv_mul _
attribute [to_additive] mul_le_of_le_inv_mul

alias le_inv_mul_iff_mul_le ↔ _ le_inv_mul_of_mul_le
attribute [to_additive] le_inv_mul_of_mul_le

alias inv_mul_le_iff_le_mul ↔ _ inv_mul_le_of_le_mul
attribute [to_additive] inv_mul_le_iff_le_mul

alias lt_inv_mul_iff_mul_lt ↔ mul_lt_of_lt_inv_mul _
attribute [to_additive] mul_lt_of_lt_inv_mul

alias lt_inv_mul_iff_mul_lt ↔ _ lt_inv_mul_of_mul_lt
attribute [to_additive] lt_inv_mul_of_mul_lt

alias inv_mul_lt_iff_lt_mul ↔ lt_mul_of_inv_mul_lt inv_mul_lt_of_lt_mul
attribute [to_additive] lt_mul_of_inv_mul_lt
attribute [to_additive] inv_mul_lt_of_lt_mul

alias lt_mul_of_inv_mul_lt ← lt_mul_of_inv_mul_lt_left
attribute [to_additive] lt_mul_of_inv_mul_lt_left

alias left.inv_le_one_iff ← inv_le_one'
attribute [to_additive neg_nonpos] inv_le_one'

alias left.one_le_inv_iff ← one_le_inv'
attribute [to_additive neg_nonneg] one_le_inv'

alias left.one_lt_inv_iff ← one_lt_inv'
attribute [to_additive neg_pos] one_lt_inv'

alias mul_lt_mul_left' ← ordered_comm_group.mul_lt_mul_left'
attribute [to_additive ordered_add_comm_group.add_lt_add_left] ordered_comm_group.mul_lt_mul_left'

alias le_of_mul_le_mul_left' ← ordered_comm_group.le_of_mul_le_mul_left
attribute [to_additive ordered_add_comm_group.le_of_add_le_add_left]
  ordered_comm_group.le_of_mul_le_mul_left

alias lt_of_mul_lt_mul_left' ← ordered_comm_group.lt_of_mul_lt_mul_left
attribute [to_additive ordered_add_comm_group.lt_of_add_lt_add_left]
  ordered_comm_group.lt_of_mul_lt_mul_left

/-  Most of the lemmas that are primed in this section appear in ordered_field. -/
/-  I (DT) did not try to minimise the assumptions. -/
section group
variables [group α] [has_le α]

section right
variables [covariant_class α α (swap (*)) (≤)] {a b c d : α}

@[simp, to_additive]
lemma div_le_div_iff_right (c : α) : a / c ≤ b / c ↔ a ≤ b :=
by simpa only [div_eq_mul_inv] using mul_le_mul_iff_right _

@[to_additive sub_le_sub_right]
lemma div_le_div_right' (h : a ≤ b) (c : α) : a / c ≤ b / c :=
(div_le_div_iff_right c).2 h

@[simp, to_additive sub_nonneg]
lemma one_le_div' : 1 ≤ a / b ↔ b ≤ a :=
by rw [← mul_le_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_nonneg ↔ le_of_sub_nonneg sub_nonneg_of_le

@[simp, to_additive sub_nonpos]
lemma div_le_one' : a / b ≤ 1 ↔ a ≤ b :=
by rw [← mul_le_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_nonpos ↔ le_of_sub_nonpos sub_nonpos_of_le

@[to_additive]
lemma le_div_iff_mul_le : a ≤ c / b ↔ a * b ≤ c :=
by rw [← mul_le_mul_iff_right b, div_eq_mul_inv, inv_mul_cancel_right]

alias le_sub_iff_add_le ↔ add_le_of_le_sub_right le_sub_right_of_add_le

@[to_additive]
lemma div_le_iff_le_mul : a / c ≤ b ↔ a ≤ b * c :=
by rw [← mul_le_mul_iff_right c, div_eq_mul_inv, inv_mul_cancel_right]

-- TODO: Should we get rid of `sub_le_iff_le_add` in favor of
-- (a renamed version of) `tsub_le_iff_right`?
@[priority 100] -- see Note [lower instance priority]
instance add_group.to_has_ordered_sub {α : Type*} [add_group α] [has_le α]
  [covariant_class α α (swap (+)) (≤)] : has_ordered_sub α :=
⟨λ a b c, sub_le_iff_le_add⟩

end right

section left
variables [covariant_class α α (*) (≤)]

variables [covariant_class α α (swap (*)) (≤)] {a b c : α}

@[simp, to_additive]
lemma div_le_div_iff_left (a : α) : a / b ≤ a / c ↔ c ≤ b :=
by rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_le_mul_iff_left a⁻¹, inv_mul_cancel_left,
    inv_mul_cancel_left, inv_le_inv_iff]

@[to_additive sub_le_sub_left]
lemma div_le_div_left' (h : a ≤ b) (c : α) : c / b ≤ c / a :=
(div_le_div_iff_left c).2 h

end left

end group

section comm_group
variables [comm_group α]

section has_le
variables [has_le α] [covariant_class α α (*) (≤)] {a b c d : α}

@[to_additive sub_le_sub_iff]
lemma div_le_div_iff' : a / b ≤ c / d ↔ a * d ≤ c * b :=
by simpa only [div_eq_mul_inv] using mul_inv_le_mul_inv_iff'

@[to_additive]
lemma le_div_iff_mul_le' : b ≤ c / a ↔ a * b ≤ c :=
by rw [le_div_iff_mul_le, mul_comm]

alias le_sub_iff_add_le' ↔ add_le_of_le_sub_left le_sub_left_of_add_le

@[to_additive]
lemma div_le_iff_le_mul' : a / b ≤ c ↔ a ≤ b * c :=
by rw [div_le_iff_le_mul, mul_comm]

alias sub_le_iff_le_add' ↔ le_add_of_sub_left_le sub_left_le_of_le_add

@[simp, to_additive]
lemma inv_le_div_iff_le_mul : b⁻¹ ≤ a / c ↔ c ≤ a * b :=
le_div_iff_mul_le.trans inv_mul_le_iff_le_mul'

@[to_additive]
lemma inv_le_div_iff_le_mul' : a⁻¹ ≤ b / c ↔ c ≤ a * b :=
by rw [inv_le_div_iff_le_mul, mul_comm]

@[to_additive]
lemma div_le_comm : a / b ≤ c ↔ a / c ≤ b := div_le_iff_le_mul'.trans div_le_iff_le_mul.symm

@[to_additive]
lemma le_div_comm : a ≤ b / c ↔ c ≤ b / a := le_div_iff_mul_le'.trans le_div_iff_mul_le.symm

end has_le

section preorder
variables [preorder α] [covariant_class α α (*) (≤)] {a b c d : α}

@[to_additive sub_le_sub]
lemma div_le_div'' (hab : a ≤ b) (hcd : c ≤ d) :
  a / d ≤ b / c :=
begin
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm b, mul_inv_le_inv_mul_iff, mul_comm],
  exact mul_le_mul' hab hcd
end

end preorder

end comm_group

/-  Most of the lemmas that are primed in this section appear in ordered_field. -/
/-  I (DT) did not try to minimise the assumptions. -/
section group
variables [group α] [has_lt α]

section right
variables [covariant_class α α (swap (*)) (<)] {a b c d : α}

@[simp, to_additive]
lemma div_lt_div_iff_right (c : α) : a / c < b / c ↔ a < b :=
by simpa only [div_eq_mul_inv] using mul_lt_mul_iff_right _

@[to_additive sub_lt_sub_right]
lemma div_lt_div_right' (h : a < b) (c : α) : a / c < b / c :=
(div_lt_div_iff_right c).2 h

@[simp, to_additive sub_pos]
lemma one_lt_div' : 1 < a / b ↔ b < a :=
by rw [← mul_lt_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_pos ↔ lt_of_sub_pos sub_pos_of_lt

@[simp, to_additive sub_neg]
lemma div_lt_one' : a / b < 1 ↔ a < b :=
by rw [← mul_lt_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_neg ↔ lt_of_sub_neg sub_neg_of_lt

alias sub_neg ← sub_lt_zero

@[to_additive]
lemma lt_div_iff_mul_lt : a < c / b ↔ a * b < c :=
by rw [← mul_lt_mul_iff_right b, div_eq_mul_inv, inv_mul_cancel_right]

alias lt_sub_iff_add_lt ↔ add_lt_of_lt_sub_right lt_sub_right_of_add_lt

@[to_additive]
lemma div_lt_iff_lt_mul : a / c < b ↔ a < b * c :=
by rw [← mul_lt_mul_iff_right c, div_eq_mul_inv, inv_mul_cancel_right]

alias sub_lt_iff_lt_add ↔ lt_add_of_sub_right_lt sub_right_lt_of_lt_add

end right

section left
variables [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (<)] {a b c : α}

@[simp, to_additive]
lemma div_lt_div_iff_left (a : α) : a / b < a / c ↔ c < b :=
by rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_lt_mul_iff_left a⁻¹, inv_mul_cancel_left,
    inv_mul_cancel_left, inv_lt_inv_iff]

@[simp, to_additive]
lemma inv_lt_div_iff_lt_mul : a⁻¹ < b / c ↔ c < a * b :=
by rw [div_eq_mul_inv, lt_mul_inv_iff_mul_lt, inv_mul_lt_iff_lt_mul]

@[to_additive sub_lt_sub_left]
lemma div_lt_div_left' (h : a < b) (c : α) : c / b < c / a :=
(div_lt_div_iff_left c).2 h

end left

end group

section comm_group
variables [comm_group α]

section has_lt
variables [has_lt α] [covariant_class α α (*) (<)] {a b c d : α}

@[to_additive sub_lt_sub_iff]
lemma div_lt_div_iff' : a / b < c / d ↔ a * d < c * b :=
by simpa only [div_eq_mul_inv] using mul_inv_lt_mul_inv_iff'

@[to_additive]
lemma lt_div_iff_mul_lt' : b < c / a ↔ a * b < c :=
by rw [lt_div_iff_mul_lt, mul_comm]

alias lt_sub_iff_add_lt' ↔ add_lt_of_lt_sub_left lt_sub_left_of_add_lt

@[to_additive]
lemma div_lt_iff_lt_mul' : a / b < c ↔ a < b * c :=
by rw [div_lt_iff_lt_mul, mul_comm]

alias sub_lt_iff_lt_add' ↔ lt_add_of_sub_left_lt sub_left_lt_of_lt_add

@[to_additive]
lemma inv_lt_div_iff_lt_mul' : b⁻¹ < a / c ↔ c < a * b :=
lt_div_iff_mul_lt.trans inv_mul_lt_iff_lt_mul'

@[to_additive]
lemma div_lt_comm : a / b < c ↔ a / c < b := div_lt_iff_lt_mul'.trans div_lt_iff_lt_mul.symm

@[to_additive]
lemma lt_div_comm : a < b / c ↔ c < b / a := lt_div_iff_mul_lt'.trans lt_div_iff_mul_lt.symm

end has_lt

section preorder
variables [preorder α] [covariant_class α α (*) (<)] {a b c d : α}

@[to_additive sub_lt_sub]
lemma div_lt_div'' (hab : a < b) (hcd : c < d) :
  a / d < b / c :=
begin
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm b, mul_inv_lt_inv_mul_iff, mul_comm],
  exact mul_lt_mul_of_lt_of_lt hab hcd
end

end preorder

end comm_group

section linear_order
variables [group α] [linear_order α]

@[simp, to_additive cmp_sub_zero]
lemma cmp_div_one' [covariant_class α α (swap (*)) (≤)] (a b : α) : cmp (a / b) 1 = cmp a b :=
by rw [← cmp_mul_right' _ _ b, one_mul, div_mul_cancel']

variables [covariant_class α α (*) (≤)]

section variable_names
variables {a b c : α}

@[to_additive]
lemma le_of_forall_one_lt_lt_mul (h : ∀ ε : α, 1 < ε → a < b * ε) : a ≤ b :=
le_of_not_lt (λ h₁, lt_irrefl a (by simpa using (h _ (lt_inv_mul_iff_lt.mpr h₁))))

@[to_additive]
lemma le_iff_forall_one_lt_lt_mul : a ≤ b ↔ ∀ ε, 1 < ε → a < b * ε :=
⟨λ h ε, lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul⟩

/-  I (DT) introduced this lemma to prove (the additive version `sub_le_sub_flip` of)
`div_le_div_flip` below.  Now I wonder what is the point of either of these lemmas... -/
@[to_additive]
lemma div_le_inv_mul_iff [covariant_class α α (swap (*)) (≤)] :
  a / b ≤ a⁻¹ * b ↔ a ≤ b :=
begin
  rw [div_eq_mul_inv, mul_inv_le_inv_mul_iff],
  exact ⟨λ h, not_lt.mp (λ k, not_lt.mpr h (mul_lt_mul_of_lt_of_lt k k)), λ h, mul_le_mul' h h⟩,
end

/-  What is the point of this lemma?  See comment about `div_le_inv_mul_iff` above. -/
@[simp, to_additive]
lemma div_le_div_flip {α : Type*} [comm_group α] [linear_order α] [covariant_class α α (*) (≤)]
  {a b : α}:
  a / b ≤ b / a ↔ a ≤ b :=
begin
  rw [div_eq_mul_inv b, mul_comm],
  exact div_le_inv_mul_iff,
end

end variable_names

end linear_order

/-!
### Linearly ordered commutative groups
-/

/-- A linearly ordered additive commutative group is an
additive commutative group with a linear order in which
addition is monotone. -/
@[protect_proj, ancestor ordered_add_comm_group linear_order]
class linear_ordered_add_comm_group (α : Type u) extends ordered_add_comm_group α, linear_order α

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined.` -/
@[protect_proj, ancestor linear_ordered_add_comm_monoid_with_top sub_neg_monoid nontrivial]
class linear_ordered_add_comm_group_with_top (α : Type*)
  extends linear_ordered_add_comm_monoid_with_top α, sub_neg_monoid α, nontrivial α :=
(neg_top : - (⊤ : α) = ⊤)
(add_neg_cancel : ∀ a:α, a ≠ ⊤ → a + (- a) = 0)

/-- A linearly ordered commutative group is a
commutative group with a linear order in which
multiplication is monotone. -/
@[protect_proj, ancestor ordered_comm_group linear_order, to_additive]
class linear_ordered_comm_group (α : Type u) extends ordered_comm_group α, linear_order α

section linear_ordered_comm_group
variables [linear_ordered_comm_group α] {a b c : α}

@[to_additive linear_ordered_add_comm_group.add_lt_add_left]
lemma linear_ordered_comm_group.mul_lt_mul_left'
  (a b : α) (h : a < b) (c : α) : c * a < c * b :=
mul_lt_mul_left' h c

@[to_additive eq_zero_of_neg_eq]
lemma eq_one_of_inv_eq' (h : a⁻¹ = a) : a = 1 :=
match lt_trichotomy a 1 with
| or.inl h₁ :=
  have 1 < a, from h ▸ one_lt_inv_of_inv h₁,
  absurd h₁ this.asymm
| or.inr (or.inl h₁) := h₁
| or.inr (or.inr h₁) :=
  have a < 1, from h ▸ inv_lt_one'.mpr h₁,
  absurd h₁ this.asymm
end

@[to_additive exists_zero_lt]
lemma exists_one_lt' [nontrivial α] : ∃ (a:α), 1 < a :=
begin
  obtain ⟨y, hy⟩ := decidable.exists_ne (1 : α),
  cases hy.lt_or_lt,
  { exact ⟨y⁻¹, one_lt_inv'.mpr h⟩ },
  { exact ⟨y, h⟩ }
end

@[priority 100, to_additive] -- see Note [lower instance priority]
instance linear_ordered_comm_group.to_no_max_order [nontrivial α] :
  no_max_order α :=
⟨ begin
    obtain ⟨y, hy⟩ : ∃ (a:α), 1 < a := exists_one_lt',
    exact λ a, ⟨a * y, lt_mul_of_one_lt_right' a hy⟩
  end ⟩

@[priority 100, to_additive] -- see Note [lower instance priority]
instance linear_ordered_comm_group.to_no_min_order [nontrivial α] : no_min_order α :=
⟨ begin
    obtain ⟨y, hy⟩ : ∃ (a:α), 1 < a := exists_one_lt',
    exact λ a, ⟨a / y, (div_lt_self_iff a).mpr hy⟩
  end ⟩

@[priority 100, to_additive] -- See note [lower instance priority]
instance linear_ordered_comm_group.to_linear_ordered_cancel_comm_monoid :
  linear_ordered_cancel_comm_monoid α :=
{ ..‹linear_ordered_comm_group α›, ..ordered_comm_group.to_ordered_cancel_comm_monoid }

end linear_ordered_comm_group

namespace add_comm_group

/-- A collection of elements in an `add_comm_group` designated as "non-negative".
This is useful for constructing an `ordered_add_commm_group`
by choosing a positive cone in an exisiting `add_comm_group`. -/
@[nolint has_nonempty_instance]
structure positive_cone (α : Type*) [add_comm_group α] :=
(nonneg          : α → Prop)
(pos             : α → Prop := λ a, nonneg a ∧ ¬ nonneg (-a))
(pos_iff         : ∀ a, pos a ↔ nonneg a ∧ ¬ nonneg (-a) . order_laws_tac)
(zero_nonneg     : nonneg 0)
(add_nonneg      : ∀ {a b}, nonneg a → nonneg b → nonneg (a + b))
(nonneg_antisymm : ∀ {a}, nonneg a → nonneg (-a) → a = 0)

/-- A positive cone in an `add_comm_group` induces a linear order if
for every `a`, either `a` or `-a` is non-negative. -/
@[nolint has_nonempty_instance]
structure total_positive_cone (α : Type*) [add_comm_group α] extends positive_cone α :=
(nonneg_decidable : decidable_pred nonneg)
(nonneg_total : ∀ a : α, nonneg a ∨ nonneg (-a))

/-- Forget that a `total_positive_cone` is total. -/
add_decl_doc total_positive_cone.to_positive_cone

end add_comm_group

namespace ordered_add_comm_group

open add_comm_group

/-- Construct an `ordered_add_comm_group` by
designating a positive cone in an existing `add_comm_group`. -/
def mk_of_positive_cone {α : Type*} [add_comm_group α] (C : positive_cone α) :
  ordered_add_comm_group α :=
{ le               := λ a b, C.nonneg (b - a),
  lt               := λ a b, C.pos (b - a),
  lt_iff_le_not_le := λ a b, by simp; rw [C.pos_iff]; simp,
  le_refl          := λ a, by simp [C.zero_nonneg],
  le_trans         := λ a b c nab nbc, by simp [-sub_eq_add_neg];
    rw ← sub_add_sub_cancel; exact C.add_nonneg nbc nab,
  le_antisymm      := λ a b nab nba, eq_of_sub_eq_zero $
    C.nonneg_antisymm nba (by rw neg_sub; exact nab),
  add_le_add_left  := λ a b nab c, by simpa [(≤), preorder.le] using nab,
  ..‹add_comm_group α› }

end ordered_add_comm_group

namespace linear_ordered_add_comm_group

open add_comm_group

/-- Construct a `linear_ordered_add_comm_group` by
designating a positive cone in an existing `add_comm_group`
such that for every `a`, either `a` or `-a` is non-negative. -/
def mk_of_positive_cone {α : Type*} [add_comm_group α] (C : total_positive_cone α) :
  linear_ordered_add_comm_group α :=
{ le_total := λ a b, by { convert C.nonneg_total (b - a), change C.nonneg _ = _, congr, simp, },
  decidable_le := λ a b, C.nonneg_decidable _,
  ..ordered_add_comm_group.mk_of_positive_cone C.to_positive_cone }

end linear_ordered_add_comm_group

section norm_num_lemmas
/- The following lemmas are stated so that the `norm_num` tactic can use them with the
expected signatures.  -/
variables [ordered_comm_group α] {a b : α}

@[to_additive neg_le_neg]
lemma inv_le_inv' : a ≤ b → b⁻¹ ≤ a⁻¹ :=
inv_le_inv_iff.mpr

@[to_additive neg_lt_neg]
lemma inv_lt_inv' : a < b → b⁻¹ < a⁻¹ :=
inv_lt_inv_iff.mpr

/-  The additive version is also a `linarith` lemma. -/
@[to_additive]
theorem inv_lt_one_of_one_lt : 1 < a → a⁻¹ < 1 :=
inv_lt_one_iff_one_lt.mpr

/-  The additive version is also a `linarith` lemma. -/
@[to_additive]
lemma inv_le_one_of_one_le : 1 ≤ a → a⁻¹ ≤ 1 :=
inv_le_one'.mpr

@[to_additive neg_nonneg_of_nonpos]
lemma one_le_inv_of_le_one :  a ≤ 1 → 1 ≤ a⁻¹ :=
one_le_inv'.mpr

end norm_num_lemmas

section

variables {β : Type*}
[group α] [preorder α] [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)]
[preorder β] {f : β → α} {s : set β}

@[to_additive] lemma monotone.inv (hf : monotone f) : antitone (λ x, (f x)⁻¹) :=
λ x y hxy, inv_le_inv_iff.2 (hf hxy)

@[to_additive] lemma antitone.inv (hf : antitone f) : monotone (λ x, (f x)⁻¹) :=
λ x y hxy, inv_le_inv_iff.2 (hf hxy)

@[to_additive] lemma monotone_on.inv (hf : monotone_on f s) :
  antitone_on (λ x, (f x)⁻¹) s :=
λ x hx y hy hxy, inv_le_inv_iff.2 (hf hx hy hxy)

@[to_additive] lemma antitone_on.inv (hf : antitone_on f s) :
  monotone_on (λ x, (f x)⁻¹) s :=
λ x hx y hy hxy, inv_le_inv_iff.2 (hf hx hy hxy)

end

section

variables {β : Type*}
[group α] [preorder α] [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (<)]
[preorder β] {f : β → α} {s : set β}

@[to_additive] lemma strict_mono.inv (hf : strict_mono f) : strict_anti (λ x, (f x)⁻¹) :=
λ x y hxy, inv_lt_inv_iff.2 (hf hxy)

@[to_additive] lemma strict_anti.inv (hf : strict_anti f) : strict_mono (λ x, (f x)⁻¹) :=
λ x y hxy, inv_lt_inv_iff.2 (hf hxy)

@[to_additive] lemma strict_mono_on.inv (hf : strict_mono_on f s) :
  strict_anti_on (λ x, (f x)⁻¹) s :=
λ x hx y hy hxy, inv_lt_inv_iff.2 (hf hx hy hxy)

@[to_additive] lemma strict_anti_on.inv (hf : strict_anti_on f s) :
  strict_mono_on (λ x, (f x)⁻¹) s :=
λ x hx y hy hxy, inv_lt_inv_iff.2 (hf hx hy hxy)

end
