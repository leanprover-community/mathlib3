/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import algebra.covariant_and_contravariant
import algebra.group.basic
import algebra.order.monoid.lemmas
import order.lattice

/-!
# Ordered Subtraction

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves lemmas relating (truncated) subtraction with an order. We provide a class
`has_ordered_sub` stating that `a - b ≤ c ↔ a ≤ c + b`.

The subtraction discussed here could both be normal subtraction in an additive group or truncated
subtraction on a canonically ordered monoid (`ℕ`, `multiset`, `part_enat`, `ennreal`, ...)

## Implementation details

`has_ordered_sub` is a mixin type-class, so that we can use the results in this file even in cases
where we don't have a `canonically_ordered_add_monoid` instance
(even though that is our main focus). Conversely, this means we can use
`canonically_ordered_add_monoid` without necessarily having to define a subtraction.

The results in this file are ordered by the type-class assumption needed to prove it.
This means that similar results might not be close to each other. Furthermore, we don't prove
implications if a bi-implication can be proven under the same assumptions.

Lemmas using this class are named using `tsub` instead of `sub` (short for "truncated subtraction").
This is to avoid naming conflicts with similar lemmas about ordered groups.

We provide a second version of most results that require `[contravariant_class α α (+) (≤)]`. In the
second version we replace this type-class assumption by explicit `add_le_cancellable` assumptions.

TODO: maybe we should make a multiplicative version of this, so that we can replace some identical
lemmas about subtraction/division in `ordered_[add_]comm_group` with these.

TODO: generalize `nat.le_of_le_of_sub_le_sub_right`, `nat.sub_le_sub_right_iff`,
  `nat.mul_self_sub_mul_self_eq`
-/

variables {α β : Type*}

/-- `has_ordered_sub α` means that `α` has a subtraction characterized by `a - b ≤ c ↔ a ≤ c + b`.
In other words, `a - b` is the least `c` such that `a ≤ b + c`.

This is satisfied both by the subtraction in additive ordered groups and by truncated subtraction
in canonically ordered monoids on many specific types.
-/
class has_ordered_sub (α : Type*) [has_le α] [has_add α] [has_sub α] :=
(tsub_le_iff_right : ∀ a b c : α, a - b ≤ c ↔ a ≤ c + b)

section has_add

variables [preorder α] [has_add α] [has_sub α] [has_ordered_sub α] {a b c d : α}

@[simp] lemma tsub_le_iff_right : a - b ≤ c ↔ a ≤ c + b :=
has_ordered_sub.tsub_le_iff_right a b c

/-- See `add_tsub_cancel_right` for the equality if `contravariant_class α α (+) (≤)`. -/
lemma add_tsub_le_right : a + b - b ≤ a :=
tsub_le_iff_right.mpr le_rfl

lemma le_tsub_add : b ≤ (b - a) + a :=
tsub_le_iff_right.mp le_rfl

end has_add

/-! ### Preorder -/

section ordered_add_comm_semigroup

section preorder
variables [preorder α]

section add_comm_semigroup
variables [add_comm_semigroup α] [has_sub α] [has_ordered_sub α] {a b c d : α}

lemma tsub_le_iff_left : a - b ≤ c ↔ a ≤ b + c :=
by rw [tsub_le_iff_right, add_comm]

lemma le_add_tsub : a ≤ b + (a - b) :=
tsub_le_iff_left.mp le_rfl

/-- See `add_tsub_cancel_left` for the equality if `contravariant_class α α (+) (≤)`. -/
lemma add_tsub_le_left : a + b - a ≤ b :=
tsub_le_iff_left.mpr le_rfl

lemma tsub_le_tsub_right (h : a ≤ b) (c : α) : a - c ≤ b - c :=
tsub_le_iff_left.mpr $ h.trans le_add_tsub

lemma tsub_le_iff_tsub_le : a - b ≤ c ↔ a - c ≤ b :=
by rw [tsub_le_iff_left, tsub_le_iff_right]

/-- See `tsub_tsub_cancel_of_le` for the equality. -/
lemma tsub_tsub_le : b - (b - a) ≤ a :=
tsub_le_iff_right.mpr le_add_tsub

section cov
variable [covariant_class α α (+) (≤)]

lemma tsub_le_tsub_left (h : a ≤ b) (c : α) : c - b ≤ c - a :=
tsub_le_iff_left.mpr $ le_add_tsub.trans $ add_le_add_right h _

lemma tsub_le_tsub (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
(tsub_le_tsub_right hab _).trans $ tsub_le_tsub_left hcd _

lemma antitone_const_tsub : antitone (λ x, c - x) :=
λ x y hxy, tsub_le_tsub rfl.le hxy

/-- See `add_tsub_assoc_of_le` for the equality. -/
lemma add_tsub_le_assoc : a + b - c ≤ a + (b - c) :=
by { rw [tsub_le_iff_left, add_left_comm], exact add_le_add_left le_add_tsub a }

/-- See `tsub_add_eq_add_tsub` for the equality. -/
lemma add_tsub_le_tsub_add : a + b - c ≤ a - c + b :=
by { rw [add_comm, add_comm _ b], exact add_tsub_le_assoc }

lemma add_le_add_add_tsub : a + b ≤ (a + c) + (b - c) :=
by { rw [add_assoc], exact add_le_add_left le_add_tsub a }

lemma le_tsub_add_add : a + b ≤ (a - c) + (b + c) :=
by { rw [add_comm a, add_comm (a - c)], exact add_le_add_add_tsub }

lemma tsub_le_tsub_add_tsub : a - c ≤ (a - b) + (b - c) :=
begin
  rw [tsub_le_iff_left, ← add_assoc, add_right_comm],
  exact le_add_tsub.trans (add_le_add_right le_add_tsub _),
end

lemma tsub_tsub_tsub_le_tsub : (c - a) - (c - b) ≤ b - a :=
begin
  rw [tsub_le_iff_left, tsub_le_iff_left, add_left_comm],
  exact le_tsub_add.trans (add_le_add_left le_add_tsub _),
end

lemma tsub_tsub_le_tsub_add {a b c : α} : a - (b - c) ≤ a - b + c :=
tsub_le_iff_right.2 $ calc
    a ≤ a - b + b : le_tsub_add
  ... ≤ a - b + (c + (b - c)) : add_le_add_left le_add_tsub _
  ... = a - b + c + (b - c) : (add_assoc _ _ _).symm

/-- See `tsub_add_tsub_comm` for the equality. -/
lemma add_tsub_add_le_tsub_add_tsub : a + b - (c + d) ≤ a - c + (b - d) :=
begin
  rw [add_comm c, tsub_le_iff_left, add_assoc, ←tsub_le_iff_left, ←tsub_le_iff_left],
  refine (tsub_le_tsub_right add_tsub_le_assoc c).trans _,
  rw [add_comm a, add_comm (a - c)],
  exact add_tsub_le_assoc,
end

/-- See `add_tsub_add_eq_tsub_left` for the equality. -/
lemma add_tsub_add_le_tsub_left : a + b - (a + c) ≤ b - c :=
by { rw [tsub_le_iff_left, add_assoc], exact add_le_add_left le_add_tsub _ }

/-- See `add_tsub_add_eq_tsub_right` for the equality. -/
lemma add_tsub_add_le_tsub_right : a + c - (b + c) ≤ a - b :=
by { rw [tsub_le_iff_left, add_right_comm], exact add_le_add_right le_add_tsub c }

end cov

/-! #### Lemmas that assume that an element is `add_le_cancellable` -/

namespace add_le_cancellable

protected lemma le_add_tsub_swap (hb : add_le_cancellable b) : a ≤ b + a - b := hb le_add_tsub

protected lemma le_add_tsub (hb : add_le_cancellable b) : a ≤ a + b - b :=
by { rw add_comm, exact hb.le_add_tsub_swap }

protected lemma le_tsub_of_add_le_left (ha : add_le_cancellable a) (h : a + b ≤ c) : b ≤ c - a :=
ha $ h.trans le_add_tsub

protected lemma le_tsub_of_add_le_right (hb : add_le_cancellable b) (h : a + b ≤ c) : a ≤ c - b :=
hb.le_tsub_of_add_le_left $ by rwa add_comm

end add_le_cancellable

/-! ### Lemmas where addition is order-reflecting -/

section contra
variable [contravariant_class α α (+) (≤)]

lemma le_add_tsub_swap : a ≤ b + a - b := contravariant.add_le_cancellable.le_add_tsub_swap

lemma le_add_tsub' : a ≤ a + b - b := contravariant.add_le_cancellable.le_add_tsub

lemma le_tsub_of_add_le_left (h : a + b ≤ c) : b ≤ c - a :=
contravariant.add_le_cancellable.le_tsub_of_add_le_left h

lemma le_tsub_of_add_le_right (h : a + b ≤ c) : a ≤ c - b :=
contravariant.add_le_cancellable.le_tsub_of_add_le_right h

end contra

end add_comm_semigroup

variables [add_comm_monoid α] [has_sub α] [has_ordered_sub α] {a b c d : α}

lemma tsub_nonpos : a - b ≤ 0 ↔ a ≤ b := by rw [tsub_le_iff_left, add_zero]

alias tsub_nonpos ↔ _ tsub_nonpos_of_le

end preorder

/-! ### Partial order -/

variables [partial_order α] [add_comm_semigroup α] [has_sub α] [has_ordered_sub α] {a b c d : α}

lemma tsub_tsub (b a c : α) : b - a - c = b - (a + c) :=
begin
  apply le_antisymm,
  { rw [tsub_le_iff_left, tsub_le_iff_left, ← add_assoc, ← tsub_le_iff_left] },
  { rw [tsub_le_iff_left, add_assoc, ← tsub_le_iff_left, ← tsub_le_iff_left] }
end

lemma tsub_add_eq_tsub_tsub (a b c : α) : a - (b + c) = a - b - c := (tsub_tsub _ _ _).symm

lemma tsub_add_eq_tsub_tsub_swap (a b c : α) : a - (b + c) = a - c - b :=
by { rw [add_comm], apply tsub_add_eq_tsub_tsub }

lemma tsub_right_comm : a - b - c = a - c - b :=
by simp_rw [← tsub_add_eq_tsub_tsub, add_comm]

/-! ### Lemmas that assume that an element is `add_le_cancellable`. -/

namespace add_le_cancellable

protected lemma tsub_eq_of_eq_add (hb : add_le_cancellable b) (h : a = c + b) : a - b = c :=
le_antisymm (tsub_le_iff_right.mpr h.le) $
  by { rw h, exact hb.le_add_tsub }

protected lemma eq_tsub_of_add_eq (hc : add_le_cancellable c) (h : a + c = b) : a = b - c :=
(hc.tsub_eq_of_eq_add h.symm).symm

protected theorem tsub_eq_of_eq_add_rev (hb : add_le_cancellable b) (h : a = b + c) : a - b = c :=
hb.tsub_eq_of_eq_add $ by rw [add_comm, h]

@[simp]
protected lemma add_tsub_cancel_right (hb : add_le_cancellable b) : a + b - b = a :=
hb.tsub_eq_of_eq_add $ by rw [add_comm]

@[simp]
protected lemma add_tsub_cancel_left (ha : add_le_cancellable a) : a + b - a = b :=
ha.tsub_eq_of_eq_add $ add_comm a b

protected lemma lt_add_of_tsub_lt_left (hb : add_le_cancellable b) (h : a - b < c) : a < b + c :=
begin
  rw [lt_iff_le_and_ne, ← tsub_le_iff_left],
  refine ⟨h.le, _⟩,
  rintro rfl,
  simpa [hb] using h,
end

protected lemma lt_add_of_tsub_lt_right (hc : add_le_cancellable c) (h : a - c < b) : a < b + c :=
begin
  rw [lt_iff_le_and_ne, ← tsub_le_iff_right],
  refine ⟨h.le, _⟩,
  rintro rfl,
  simpa [hc] using h,
end

protected lemma lt_tsub_of_add_lt_right (hc : add_le_cancellable c) (h : a + c < b) : a < b - c :=
(hc.le_tsub_of_add_le_right h.le).lt_of_ne $ by { rintro rfl, exact h.not_le le_tsub_add }

protected lemma lt_tsub_of_add_lt_left (ha : add_le_cancellable a) (h : a + c < b) : c < b - a :=
ha.lt_tsub_of_add_lt_right $ by rwa add_comm

end add_le_cancellable

/-! #### Lemmas where addition is order-reflecting. -/

section contra
variable [contravariant_class α α (+) (≤)]

lemma tsub_eq_of_eq_add (h : a = c + b) : a - b = c :=
contravariant.add_le_cancellable.tsub_eq_of_eq_add h

lemma eq_tsub_of_add_eq (h : a + c = b) : a = b - c :=
contravariant.add_le_cancellable.eq_tsub_of_add_eq h

lemma tsub_eq_of_eq_add_rev (h : a = b + c) : a - b = c :=
contravariant.add_le_cancellable.tsub_eq_of_eq_add_rev h

@[simp]
lemma add_tsub_cancel_right (a b : α) : a + b - b = a :=
contravariant.add_le_cancellable.add_tsub_cancel_right

@[simp]
lemma add_tsub_cancel_left (a b : α) : a + b - a = b :=
contravariant.add_le_cancellable.add_tsub_cancel_left

lemma lt_add_of_tsub_lt_left (h : a - b < c) : a < b + c :=
contravariant.add_le_cancellable.lt_add_of_tsub_lt_left h

lemma lt_add_of_tsub_lt_right (h : a - c < b) : a < b + c :=
contravariant.add_le_cancellable.lt_add_of_tsub_lt_right h

/-- This lemma (and some of its corollaries) also holds for `ennreal`, but this proof doesn't work
for it. Maybe we should add this lemma as field to `has_ordered_sub`? -/
lemma lt_tsub_of_add_lt_left : a + c < b → c < b - a :=
contravariant.add_le_cancellable.lt_tsub_of_add_lt_left

lemma lt_tsub_of_add_lt_right : a + c < b → a < b - c :=
contravariant.add_le_cancellable.lt_tsub_of_add_lt_right

end contra

section both
variables [covariant_class α α (+) (≤)] [contravariant_class α α (+) (≤)]

lemma add_tsub_add_eq_tsub_right (a c b : α) : (a + c) - (b + c) = a - b :=
begin
  refine add_tsub_add_le_tsub_right.antisymm (tsub_le_iff_right.2 $ le_of_add_le_add_right _), swap,
  rw add_assoc,
  exact le_tsub_add,
end

lemma add_tsub_add_eq_tsub_left (a b c : α) : (a + b) - (a + c) = b - c :=
by rw [add_comm a b, add_comm a c, add_tsub_add_eq_tsub_right]

end both

end ordered_add_comm_semigroup

/-! ### Lemmas in a linearly ordered monoid. -/
section linear_order
variables {a b c d : α} [linear_order α] [add_comm_semigroup α] [has_sub α] [has_ordered_sub α]

/-- See `lt_of_tsub_lt_tsub_right_of_le` for a weaker statement in a partial order. -/
lemma lt_of_tsub_lt_tsub_right (h : a - c < b - c) : a < b :=
lt_imp_lt_of_le_imp_le (λ h, tsub_le_tsub_right h c) h

/-- See `lt_tsub_iff_right_of_le` for a weaker statement in a partial order. -/
lemma lt_tsub_iff_right : a < b - c ↔ a + c < b :=
lt_iff_lt_of_le_iff_le tsub_le_iff_right

/-- See `lt_tsub_iff_left_of_le` for a weaker statement in a partial order. -/
lemma lt_tsub_iff_left : a < b - c ↔ c + a < b :=
lt_iff_lt_of_le_iff_le tsub_le_iff_left

lemma lt_tsub_comm : a < b - c ↔ c < b - a :=
lt_tsub_iff_left.trans lt_tsub_iff_right.symm

section cov
variable [covariant_class α α (+) (≤)]

/-- See `lt_of_tsub_lt_tsub_left_of_le` for a weaker statement in a partial order. -/
lemma lt_of_tsub_lt_tsub_left (h : a - b < a - c) : c < b :=
lt_imp_lt_of_le_imp_le (λ h, tsub_le_tsub_left h a) h

end cov

end linear_order

section ordered_add_comm_monoid
variables [partial_order α] [add_comm_monoid α] [has_sub α] [has_ordered_sub α]

@[simp] lemma tsub_zero (a : α) : a - 0 = a :=
add_le_cancellable.tsub_eq_of_eq_add add_le_cancellable_zero (add_zero _).symm

end ordered_add_comm_monoid
