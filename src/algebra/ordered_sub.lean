/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import algebra.ordered_monoid
/-!
# Ordered Subtraction

This file proves lemmas relating (truncated) subtraction with an order. We provide a class
 `has_ordered_sub` stating that `a - b ≤ c ↔ a ≤ c + b`.

The subtraction discussed here could both be normal subtraction in an additive group or truncated
subtraction on a canonically ordered monoid (`ℕ`, `multiset`, `enat`, `ennreal`, ...)

## Implementation details

`has_ordered_sub` is a mixin type-class, so that we can use the results in this file even in cases
where we don't have a `canonically_ordered_add_monoid` instance
(even though that is our main focus). Conversely, this means we can use
`canonically_ordered_add_monoid` without necessarily having to define a subtraction.

The results in this file are ordered by the type-class assumption needed to prove it.
This means that similar results might not be close to each other. Furthermore, we don't prove
implications if a bi-implication can be proven under the same assumptions.

Many results about this subtraction are primed, to not conflict with similar lemmas about ordered
groups.

We provide a second version of most results that require `[contravariant_class α α (+) (≤)]`. In the
second version we replace this type-class assumption by explicit `add_le_cancellable` assumptions.

TODO: maybe we should make a multiplicative version of this, so that we can replace some identical
lemmas about subtraction/division in `ordered_[add_]comm_group` with these.

-/

variables {α : Type*}

/-- `has_ordered_sub α` means that `α` has a subtraction characterized by `a - b ≤ c ↔ a ≤ c + b`.
In other words, `a - b` is the least `c` such that `a ≤ b + c`.

This is satisfied both by the subtraction in additive ordered groups and by truncated subtraction
in canonically ordered monoids on many specific types.
-/
class has_ordered_sub (α : Type*) [preorder α] [has_add α] [has_sub α] :=
(sub_le_iff_right : ∀ a b c : α, a - b ≤ c ↔ a ≤ c + b)

section ordered_add_comm_monoid
variables {a b c d : α} [partial_order α] [add_comm_monoid α] [has_sub α] [has_ordered_sub α]

@[simp] lemma sub_le_iff_right : a - b ≤ c ↔ a ≤ c + b :=
has_ordered_sub.sub_le_iff_right a b c

lemma sub_le_iff_left : a - b ≤ c ↔ a ≤ b + c :=
by rw [sub_le_iff_right, add_comm]

lemma le_add_sub : a ≤ b + (a - b) :=
sub_le_iff_left.mp le_rfl

/-- See `add_sub_cancel_left` for the equality if `contravariant_class α α (+) (≤)`. -/
lemma add_sub_le_left : a + b - a ≤ b :=
sub_le_iff_left.mpr le_rfl

/-- See `add_sub_cancel_right` for the equality if `contravariant_class α α (+) (≤)`. -/
lemma add_sub_le_right : a + b - b ≤ a :=
sub_le_iff_right.mpr le_rfl

lemma le_sub_add : b ≤ (b - a) + a :=
sub_le_iff_right.mp le_rfl

lemma sub_le_sub_right' (h : a ≤ b) (c : α) : a - c ≤ b - c :=
sub_le_iff_left.mpr $ h.trans le_add_sub

lemma sub_le_iff_sub_le : a - b ≤ c ↔ a - c ≤ b :=
by rw [sub_le_iff_left, sub_le_iff_right]

lemma sub_sub' (b a c : α) : b - a - c = b - (a + c) :=
begin
  apply le_antisymm,
  { rw [sub_le_iff_left, sub_le_iff_left, ← add_assoc, ← sub_le_iff_left] },
  { rw [sub_le_iff_left, add_assoc, ← sub_le_iff_left, ← sub_le_iff_left] }
end

/-- See `sub_sub_cancel_of_le` for the equality. -/
lemma sub_sub_le : b - (b - a) ≤ a :=
sub_le_iff_right.mpr le_add_sub

section cov
variable [covariant_class α α (+) (≤)]

lemma sub_le_sub_left' (h : a ≤ b) (c : α) : c - b ≤ c - a :=
sub_le_iff_left.mpr $ le_add_sub.trans $ add_le_add_right h _

lemma sub_le_sub' (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
(sub_le_sub_right' hab _).trans $ sub_le_sub_left' hcd _

lemma sub_add_eq_sub_sub' : a - (b + c) = a - b - c :=
begin
  refine le_antisymm (sub_le_iff_left.mpr _)
    (sub_le_iff_left.mpr $ sub_le_iff_left.mpr _),
  { rw [add_assoc], refine le_trans le_add_sub (add_le_add_left le_add_sub _) },
  { rw [← add_assoc], apply le_add_sub }
end

lemma sub_add_eq_sub_sub_swap' : a - (b + c) = a - c - b :=
by { rw [add_comm], exact sub_add_eq_sub_sub' }

lemma add_le_add_add_sub : a + b ≤ (a + c) + (b - c) :=
by { rw [add_assoc], exact add_le_add_left le_add_sub a }

lemma sub_right_comm' : a - b - c = a - c - b :=
by simp_rw [← sub_add_eq_sub_sub', add_comm]

/-- See `add_sub_assoc_of_le` for the equality. -/
lemma add_sub_le_assoc : a + b - c ≤ a + (b - c) :=
by { rw [sub_le_iff_left, add_left_comm], exact add_le_add_left le_add_sub a }

lemma le_sub_add_add : a + b ≤ (a - c) + (b + c) :=
by { rw [add_comm a, add_comm (a - c)], exact add_le_add_add_sub }

lemma sub_le_sub_add_sub : a - c ≤ (a - b) + (b - c) :=
begin
  rw [sub_le_iff_left, ← add_assoc, add_right_comm],
  refine le_add_sub.trans (add_le_add_right le_add_sub _),
end

lemma sub_sub_sub_le_sub : (c - a) - (c - b) ≤ b - a :=
begin
  rw [sub_le_iff_left, sub_le_iff_left, add_left_comm],
  refine le_sub_add.trans (add_le_add_left le_add_sub _),
end

end cov

/-! Lemmas that assume that an element is `add_le_cancellable`. -/
namespace add_le_cancellable

protected lemma le_add_sub_swap (hb : add_le_cancellable b) : a ≤ b + a - b :=
hb le_add_sub

protected lemma le_add_sub (hb : add_le_cancellable b) : a ≤ a + b - b :=
by { rw [add_comm], exact hb.le_add_sub_swap }

protected lemma sub_eq_of_eq_add (hb : add_le_cancellable b) (h : a = c + b) : a - b = c :=
le_antisymm (sub_le_iff_right.mpr h.le) $
  by { rw h, exact hb.le_add_sub }

protected lemma eq_sub_of_add_eq (hc : add_le_cancellable c) (h : a + c = b) : a = b - c :=
(hc.sub_eq_of_eq_add h.symm).symm

@[simp]
protected lemma add_sub_cancel_right (hb : add_le_cancellable b) : a + b - b = a :=
hb.sub_eq_of_eq_add $ by rw [add_comm]

@[simp]
protected lemma add_sub_cancel_left (ha : add_le_cancellable a) : a + b - a = b :=
ha.sub_eq_of_eq_add $ add_comm a b

protected lemma le_sub_of_add_le_left (ha : add_le_cancellable a) (h : a + b ≤ c) : b ≤ c - a :=
ha $ h.trans le_add_sub

protected lemma le_sub_of_add_le_right (hb : add_le_cancellable b) (h : a + b ≤ c) : a ≤ c - b :=
hb.le_sub_of_add_le_left $ by rwa [add_comm]

protected lemma lt_add_of_sub_lt_left (hb : add_le_cancellable b) (h : a - b < c) : a < b + c :=
begin
  rw [lt_iff_le_and_ne, ← sub_le_iff_left],
  refine ⟨h.le, _⟩,
  rintro rfl,
  simpa [hb] using h,
end

protected lemma lt_add_of_sub_lt_right (hc : add_le_cancellable c) (h : a - c < b) : a < b + c :=
begin
  rw [lt_iff_le_and_ne, ← sub_le_iff_right],
  refine ⟨h.le, _⟩,
  rintro rfl,
  simpa [hc] using h,
end

end add_le_cancellable

/-! Lemmas where addition is order-reflecting. -/

section contra
variable [contravariant_class α α (+) (≤)]

lemma le_add_sub_swap : a ≤ b + a - b :=
contravariant.add_le_cancellable.le_add_sub_swap

lemma le_add_sub' : a ≤ a + b - b :=
contravariant.add_le_cancellable.le_add_sub

lemma sub_eq_of_eq_add'' (h : a = c + b) : a - b = c :=
contravariant.add_le_cancellable.sub_eq_of_eq_add h

lemma eq_sub_of_add_eq'' (h : a + c = b) : a = b - c :=
contravariant.add_le_cancellable.eq_sub_of_add_eq h

@[simp]
lemma add_sub_cancel_right : a + b - b = a :=
contravariant.add_le_cancellable.add_sub_cancel_right

@[simp]
lemma add_sub_cancel_left : a + b - a = b :=
contravariant.add_le_cancellable.add_sub_cancel_left

lemma le_sub_of_add_le_left' (h : a + b ≤ c) : b ≤ c - a :=
contravariant.add_le_cancellable.le_sub_of_add_le_left h

lemma le_sub_of_add_le_right' (h : a + b ≤ c) : a ≤ c - b :=
contravariant.add_le_cancellable.le_sub_of_add_le_right h

lemma lt_add_of_sub_lt_left' (h : a - b < c) : a < b + c :=
contravariant.add_le_cancellable.lt_add_of_sub_lt_left h

lemma lt_add_of_sub_lt_right' (h : a - c < b) : a < b + c :=
contravariant.add_le_cancellable.lt_add_of_sub_lt_right h

end contra

section both
variables [covariant_class α α (+) (≤)] [contravariant_class α α (+) (≤)]

lemma add_sub_add_right_eq_sub' : (a + c) - (b + c) = a - b :=
begin
  apply le_antisymm,
  { rw [sub_le_iff_left, add_right_comm], exact add_le_add_right le_add_sub c },
  { rw [sub_le_iff_left, add_comm b],
    apply le_of_add_le_add_right,
    rw [add_assoc],
    exact le_sub_add }
end

lemma add_sub_add_eq_sub_left' (a b c : α) : (a + b) - (a + c) = b - c :=
by rw [add_comm a b, add_comm a c, add_sub_add_right_eq_sub']

end both

end ordered_add_comm_monoid

/-! Lemmas in a linearly ordered monoid. -/
section linear_order
variables {a b c d : α} [linear_order α] [add_comm_monoid α] [has_sub α] [has_ordered_sub α]

/-- See `lt_of_sub_lt_sub_right_of_le` for a weaker statement in a partial order. -/
lemma lt_of_sub_lt_sub_right (h : a - c < b - c) : a < b :=
lt_imp_lt_of_le_imp_le (λ h, sub_le_sub_right' h c) h

section cov
variable [covariant_class α α (+) (≤)]

/-- See `lt_of_sub_lt_sub_left_of_le` for a weaker statement in a partial order. -/
lemma lt_of_sub_lt_sub_left (h : a - b < a - c) : c < b :=
lt_imp_lt_of_le_imp_le (λ h, sub_le_sub_left' h a) h

end cov

end linear_order

/-! Lemmas in a canonically ordered monoid. -/

section canonically_ordered_add_monoid
variables [canonically_ordered_add_monoid α] [has_sub α] [has_ordered_sub α] {a b c d : α}

lemma add_sub_cancel_of_le (h : a ≤ b) : a + (b - a) = b :=
begin
  refine le_antisymm _ le_add_sub,
  obtain ⟨c, rfl⟩ := le_iff_exists_add.1 h,
  exact add_le_add_left add_sub_le_left a,
end

lemma sub_add_cancel_of_le (h : a ≤ b) : b - a + a = b :=
by { rw [add_comm], exact add_sub_cancel_of_le h }

lemma add_sub_cancel_iff_le : a + (b - a) = b ↔ a ≤ b :=
⟨λ h, le_iff_exists_add.mpr ⟨b - a, h.symm⟩, add_sub_cancel_of_le⟩

lemma sub_add_cancel_iff_le : b - a + a = b ↔ a ≤ b :=
by { rw [add_comm], exact add_sub_cancel_iff_le }

lemma add_le_of_le_sub_right_of_le (h : b ≤ c) (h2 : a ≤ c - b) : a + b ≤ c :=
(add_le_add_right h2 b).trans_eq $ sub_add_cancel_of_le h

lemma add_le_of_le_sub_left_of_le (h : a ≤ c) (h2 : b ≤ c - a) : a + b ≤ c :=
(add_le_add_left h2 a).trans_eq $ add_sub_cancel_of_le h

lemma sub_le_sub_iff_right' (h : c ≤ b) : a - c ≤ b - c ↔ a ≤ b :=
by rw [sub_le_iff_right, sub_add_cancel_of_le h]

lemma sub_left_inj' (h1 : c ≤ a) (h2 : c ≤ b) : a - c = b - c ↔ a = b :=
by simp_rw [le_antisymm_iff, sub_le_sub_iff_right' h1, sub_le_sub_iff_right' h2]

/-- See `lt_of_sub_lt_sub_right` for a stronger statement in a linear order. -/
lemma lt_of_sub_lt_sub_right_of_le (h : c ≤ b) (h2 : a - c < b - c) : a < b :=
by { refine ((sub_le_sub_iff_right' h).mp h2.le).lt_of_ne _, rintro rfl, exact h2.false }

lemma sub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b :=
by rw [← nonpos_iff_eq_zero, sub_le_iff_left, add_zero]

@[simp] lemma sub_self' : a - a = 0 :=
sub_eq_zero_iff_le.mpr le_rfl

@[simp] lemma sub_le_self' : a - b ≤ a :=
sub_le_iff_left.mpr $ le_add_left le_rfl

@[simp] lemma sub_zero' : a - 0 = a :=
le_antisymm sub_le_self' $ le_add_sub.trans_eq $ zero_add _

@[simp] lemma zero_sub' : 0 - a = 0 :=
sub_eq_zero_iff_le.mpr $ zero_le a

lemma sub_self_add (a b : α) : a - (a + b) = 0 :=
by { rw [sub_eq_zero_iff_le], apply self_le_add_right }

lemma sub_inj_left (h₁ : a ≤ b) (h₂ : a ≤ c) (h₃ : b - a = c - a) : b = c :=
by rw [← sub_add_cancel_of_le h₁, ← sub_add_cancel_of_le h₂, h₃]

lemma sub_pos_iff_not_le : 0 < a - b ↔ ¬ a ≤ b :=
by rw [pos_iff_ne_zero, ne.def, sub_eq_zero_iff_le]

lemma sub_pos_of_lt' (h : a < b) : 0 < b - a :=
sub_pos_iff_not_le.mpr h.not_le

lemma sub_add_sub_cancel'' (hab : b ≤ a) (hbc : c ≤ b) : (a - b) + (b - c) = a - c :=
begin
  convert sub_add_cancel_of_le (sub_le_sub_right' hab c) using 2,
  rw [sub_sub', add_sub_cancel_of_le hbc],
end

lemma sub_sub_sub_cancel_right' (h : c ≤ b) : (a - c) - (b - c) = a - b :=
by rw [sub_sub', add_sub_cancel_of_le h]

/-! Lemmas that assume that an element is `add_le_cancellable`. -/

namespace add_le_cancellable
protected lemma eq_sub_iff_add_eq_of_le (hc : add_le_cancellable c) (h : c ≤ b) :
  a = b - c ↔ a + c = b :=
begin
  split,
  { rintro rfl, exact sub_add_cancel_of_le h },
  { rintro rfl, exact (hc.add_sub_cancel_right).symm }
end

protected lemma sub_eq_iff_eq_add_of_le (hb : add_le_cancellable b) (h : b ≤ a) :
  a - b = c ↔ a = c + b :=
by rw [eq_comm, hb.eq_sub_iff_add_eq_of_le h, eq_comm]

protected lemma add_sub_assoc_of_le (hc : add_le_cancellable c) (h : c ≤ b) (a : α) :
  a + b - c = a + (b - c) :=
by conv_lhs { rw [← add_sub_cancel_of_le h, add_comm c, ← add_assoc,
  hc.add_sub_cancel_right] }

protected lemma sub_add_eq_add_sub (hb : add_le_cancellable b) (h : b ≤ a) :
  a - b + c = a + c - b :=
by rw [add_comm a, hb.add_sub_assoc_of_le h, add_comm]

protected lemma sub_sub_assoc (hbc : add_le_cancellable (b - c)) (h₁ : b ≤ a) (h₂ : c ≤ b) :
  a - (b - c) = a - b + c :=
by rw [hbc.sub_eq_iff_eq_add_of_le (sub_le_self'.trans h₁), add_assoc,
  add_sub_cancel_of_le h₂, sub_add_cancel_of_le h₁]

protected lemma le_sub_iff_left (ha : add_le_cancellable a) (h : a ≤ c) : b ≤ c - a ↔ a + b ≤ c :=
⟨add_le_of_le_sub_left_of_le h, ha.le_sub_of_add_le_left⟩

protected lemma le_sub_iff_right (ha : add_le_cancellable a) (h : a ≤ c) : b ≤ c - a ↔ b + a ≤ c :=
by { rw [add_comm], exact ha.le_sub_iff_left h }

protected lemma sub_lt_iff_left (hb : add_le_cancellable b) (hba : b ≤ a) :
  a - b < c ↔ a < b + c :=
begin
  refine ⟨hb.lt_add_of_sub_lt_left, _⟩,
  intro h, refine (sub_le_iff_left.mpr h.le).lt_of_ne _,
  rintro rfl, exact h.ne' (add_sub_cancel_of_le hba)
end

protected lemma sub_lt_iff_right (hb : add_le_cancellable b) (hba : b ≤ a) :
  a - b < c ↔ a < c + b :=
by { rw [add_comm], exact hb.sub_lt_iff_left hba }

protected lemma lt_sub_of_add_lt_right (hc : add_le_cancellable c) (h : a + c < b) : a < b - c :=
begin
  apply lt_of_le_of_ne,
  { rw [← add_sub_cancel_of_le h.le, add_right_comm, add_assoc],
    rw [hc.add_sub_assoc_of_le], refine le_self_add, refine le_add_self },
  { rintro rfl, apply h.not_le, exact le_sub_add }
end

protected lemma lt_sub_of_add_lt_left (ha : add_le_cancellable a) (h : a + c < b) : c < b - a :=
by { apply ha.lt_sub_of_add_lt_right, rwa add_comm }

protected lemma sub_lt_iff_sub_lt (hb : add_le_cancellable b) (hc : add_le_cancellable c)
  (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < c ↔ a - c < b :=
by rw [hb.sub_lt_iff_left h₁, hc.sub_lt_iff_right h₂]

protected lemma le_sub_iff_le_sub (ha : add_le_cancellable a) (hc : add_le_cancellable c)
  (h₁ : a ≤ b) (h₂ : c ≤ b) : a ≤ b - c ↔ c ≤ b - a :=
by rw [ha.le_sub_iff_left h₁, hc.le_sub_iff_right h₂]

protected lemma lt_sub_iff_right_of_le (hc : add_le_cancellable c) (h : c ≤ b) :
  a < b - c ↔ a + c < b :=
begin
  refine ⟨_, hc.lt_sub_of_add_lt_right⟩,
  intro h2,
  refine (add_le_of_le_sub_right_of_le h h2.le).lt_of_ne _,
  rintro rfl,
  apply h2.not_le,
  rw [hc.add_sub_cancel_right]
end

protected lemma lt_sub_iff_left_of_le (hc : add_le_cancellable c) (h : c ≤ b) :
  a < b - c ↔ c + a < b :=
by { rw [add_comm], exact hc.lt_sub_iff_right_of_le h }

protected lemma lt_of_sub_lt_sub_left_of_le (hb : add_le_cancellable b) (hca : c ≤ a)
  (h : a - b < a - c) : c < b :=
begin
  conv_lhs at h { rw [← sub_add_cancel_of_le hca] },
  exact lt_of_add_lt_add_left (hb.lt_add_of_sub_lt_right h),
end

protected lemma sub_le_sub_iff_left (ha : add_le_cancellable a) (hc : add_le_cancellable c)
  (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b :=
begin
  refine ⟨_, λ h, sub_le_sub_left' h a⟩,
  rw [sub_le_iff_left, ← hc.add_sub_assoc_of_le h,
    hc.le_sub_iff_right (h.trans le_add_self), add_comm b],
  apply ha,
end

protected lemma sub_right_inj (ha : add_le_cancellable a) (hb : add_le_cancellable b)
  (hc : add_le_cancellable c) (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c :=
by simp_rw [le_antisymm_iff, ha.sub_le_sub_iff_left hb hba, ha.sub_le_sub_iff_left hc hca, and_comm]

protected lemma sub_lt_sub_right_of_le (hc : add_le_cancellable c) (h : c ≤ a) (h2 : a < b) :
  a - c < b - c :=
by { apply hc.lt_sub_of_add_lt_left, rwa [add_sub_cancel_of_le h] }

protected lemma sub_inj_right (hab : add_le_cancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a)
  (h₃ : a - b = a - c) : b = c :=
by { rw ← hab.inj, rw [sub_add_cancel_of_le h₁, h₃, sub_add_cancel_of_le h₂] }

protected lemma sub_lt_sub_iff_left_of_le_of_le (hb : add_le_cancellable b)
  (hab : add_le_cancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < a - c ↔ c < b :=
begin
  refine ⟨hb.lt_of_sub_lt_sub_left_of_le h₂, _⟩,
  intro h, refine (sub_le_sub_left' h.le _).lt_of_ne _,
  rintro h2, exact h.ne' (hab.sub_inj_right h₁ h₂ h2)
end

@[simp] protected lemma add_sub_sub_cancel (hac : add_le_cancellable (a - c)) (h : c ≤ a) :
  (a + b) - (a - c) = b + c :=
(hac.sub_eq_iff_eq_add_of_le $ sub_le_self'.trans le_self_add).mpr $
  by rw [add_assoc, add_sub_cancel_of_le h, add_comm]

protected lemma sub_sub_cancel_of_le (hba : add_le_cancellable (b - a)) (h : a ≤ b) :
  b - (b - a) = a :=
by rw [hba.sub_eq_iff_eq_add_of_le sub_le_self', add_sub_cancel_of_le h]

end add_le_cancellable

section contra
/-! Lemmas where addition is order-reflecting. -/
variable [contravariant_class α α (+) (≤)]

lemma eq_sub_iff_add_eq_of_le (h : c ≤ b) : a = b - c ↔ a + c = b :=
contravariant.add_le_cancellable.eq_sub_iff_add_eq_of_le h

lemma sub_eq_iff_eq_add_of_le (h : b ≤ a) : a - b = c ↔ a = c + b :=
contravariant.add_le_cancellable.sub_eq_iff_eq_add_of_le h

/-- See `add_sub_le_assoc` for an inequality. -/
lemma add_sub_assoc_of_le (h : c ≤ b) (a : α) : a + b - c = a + (b - c) :=
contravariant.add_le_cancellable.add_sub_assoc_of_le h a

lemma sub_add_eq_add_sub' (h : b ≤ a) : a - b + c = a + c - b :=
contravariant.add_le_cancellable.sub_add_eq_add_sub h

lemma sub_sub_assoc (h₁ : b ≤ a) (h₂ : c ≤ b) : a - (b - c) = a - b + c :=
contravariant.add_le_cancellable.sub_sub_assoc h₁ h₂

lemma le_sub_iff_left (h : a ≤ c) : b ≤ c - a ↔ a + b ≤ c :=
contravariant.add_le_cancellable.le_sub_iff_left h

lemma le_sub_iff_right (h : a ≤ c) : b ≤ c - a ↔ b + a ≤ c :=
contravariant.add_le_cancellable.le_sub_iff_right h

lemma sub_lt_iff_left (hbc : b ≤ a) : a - b < c ↔ a < b + c :=
contravariant.add_le_cancellable.sub_lt_iff_left hbc

lemma sub_lt_iff_right (hbc : b ≤ a) : a - b < c ↔ a < c + b :=
contravariant.add_le_cancellable.sub_lt_iff_right hbc

/-- This lemma (and some of its corollaries also holds for `ennreal`,
  but this proof doesn't work for it.
  Maybe we should add this lemma as field to `has_ordered_sub`? -/
lemma lt_sub_of_add_lt_right (h : a + c < b) : a < b - c :=
contravariant.add_le_cancellable.lt_sub_of_add_lt_right h

lemma lt_sub_of_add_lt_left (h : a + c < b) : c < b - a :=
contravariant.add_le_cancellable.lt_sub_of_add_lt_left h

lemma sub_lt_iff_sub_lt (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < c ↔ a - c < b :=
contravariant.add_le_cancellable.sub_lt_iff_sub_lt contravariant.add_le_cancellable h₁ h₂

lemma le_sub_iff_le_sub (h₁ : a ≤ b) (h₂ : c ≤ b) : a ≤ b - c ↔ c ≤ b - a :=
contravariant.add_le_cancellable.le_sub_iff_le_sub contravariant.add_le_cancellable h₁ h₂

/-- See `lt_sub_iff_right` for a stronger statement in a linear order. -/
lemma lt_sub_iff_right_of_le (h : c ≤ b) : a < b - c ↔ a + c < b :=
contravariant.add_le_cancellable.lt_sub_iff_right_of_le h

/-- See `lt_sub_iff_left` for a stronger statement in a linear order. -/
lemma lt_sub_iff_left_of_le (h : c ≤ b) : a < b - c ↔ c + a < b :=
contravariant.add_le_cancellable.lt_sub_iff_left_of_le h

/-- See `lt_of_sub_lt_sub_left` for a stronger statement in a linear order. -/
lemma lt_of_sub_lt_sub_left_of_le (hca : c ≤ a) (h : a - b < a - c) : c < b :=
contravariant.add_le_cancellable.lt_of_sub_lt_sub_left_of_le hca h

lemma sub_le_sub_iff_left' (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b :=
contravariant.add_le_cancellable.sub_le_sub_iff_left contravariant.add_le_cancellable h

lemma sub_right_inj' (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c :=
contravariant.add_le_cancellable.sub_right_inj contravariant.add_le_cancellable
  contravariant.add_le_cancellable hba hca

lemma sub_lt_sub_right_of_le (h : c ≤ a) (h2 : a < b) : a - c < b - c :=
contravariant.add_le_cancellable.sub_lt_sub_right_of_le h h2

lemma sub_inj_right (h₁ : b ≤ a) (h₂ : c ≤ a) (h₃ : a - b = a - c) : b = c :=
contravariant.add_le_cancellable.sub_inj_right h₁ h₂ h₃

/-- See `sub_lt_sub_iff_left_of_le` for a stronger statement in a linear order. -/
lemma sub_lt_sub_iff_left_of_le_of_le (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < a - c ↔ c < b :=
contravariant.add_le_cancellable.sub_lt_sub_iff_left_of_le_of_le
  contravariant.add_le_cancellable h₁ h₂

@[simp] lemma add_sub_sub_cancel' (h : c ≤ a) : (a + b) - (a - c) = b + c :=
contravariant.add_le_cancellable.add_sub_sub_cancel h

/-- See `sub_sub_le` for an inequality. -/
lemma sub_sub_cancel_of_le (h : a ≤ b) : b - (b - a) = a :=
contravariant.add_le_cancellable.sub_sub_cancel_of_le h

end contra

end canonically_ordered_add_monoid

/-! Lemmas in a linearly canonically ordered monoid. -/

section canonically_linear_ordered_add_monoid
variables [canonically_linear_ordered_add_monoid α] [has_sub α] [has_ordered_sub α] {a b c d : α}

lemma sub_pos_iff_lt : 0 < a - b ↔ b < a :=
by rw [sub_pos_iff_not_le, not_le]

lemma sub_eq_sub_min (a b : α) : a - b = a - min a b :=
begin
  cases le_total a b with h h,
  { rw [min_eq_left h, sub_self', sub_eq_zero_iff_le.mpr h] },
  { rw [min_eq_right h] },
end

namespace add_le_cancellable

protected lemma lt_sub_iff_right (hc : add_le_cancellable c) : a < b - c ↔ a + c < b :=
⟨lt_imp_lt_of_le_imp_le sub_le_iff_right.mpr, hc.lt_sub_of_add_lt_right⟩

protected lemma lt_sub_iff_left (hc : add_le_cancellable c) : a < b - c ↔ c + a < b :=
⟨lt_imp_lt_of_le_imp_le sub_le_iff_left.mpr, hc.lt_sub_of_add_lt_left⟩

protected lemma sub_lt_sub_iff_right (hc : add_le_cancellable c) (h : c ≤ a) :
  a - c < b - c ↔ a < b :=
by rw [hc.lt_sub_iff_left, add_sub_cancel_of_le h]

protected lemma lt_sub_iff_lt_sub (ha : add_le_cancellable a) (hc : add_le_cancellable c) :
  a < b - c ↔ c < b - a :=
by rw [hc.lt_sub_iff_left, ha.lt_sub_iff_right]

protected lemma sub_lt_self (ha : add_le_cancellable a) (hb : add_le_cancellable b)
  (h₁ : 0 < a) (h₂ : 0 < b) : a - b < a :=
begin
  refine sub_le_self'.lt_of_ne _,
  intro h,
  rw [← h, sub_pos_iff_lt] at h₁,
  have := h.ge,
  rw [hb.le_sub_iff_left h₁.le, ha.add_le_iff_nonpos_left] at this,
  exact h₂.not_le this,
end

protected lemma sub_lt_self_iff (ha : add_le_cancellable a) (hb : add_le_cancellable b) :
  a - b < a ↔ 0 < a ∧ 0 < b :=
begin
  refine ⟨_, λ h, ha.sub_lt_self hb h.1 h.2⟩,
  intro h,
  refine ⟨(zero_le _).trans_lt h, (zero_le b).lt_of_ne _⟩,
  rintro rfl,
  rw [sub_zero'] at h,
  exact h.false
end

/-- See `lt_sub_iff_left_of_le_of_le` for a weaker statement in a partial order. -/
protected lemma sub_lt_sub_iff_left_of_le (ha : add_le_cancellable a) (hb : add_le_cancellable b)
  (h : b ≤ a) : a - b < a - c ↔ c < b :=
lt_iff_lt_of_le_iff_le $ ha.sub_le_sub_iff_left hb h

end add_le_cancellable

section contra
variable [contravariant_class α α (+) (≤)]

/-- See `lt_sub_iff_right_of_le` for a weaker statement in a partial order.
This lemma also holds for `ennreal`, but we need a different proof for that. -/
lemma lt_sub_iff_right : a < b - c ↔ a + c < b :=
contravariant.add_le_cancellable.lt_sub_iff_right

/-- See `lt_sub_iff_left_of_le` for a weaker statement in a partial order.
This lemma also holds for `ennreal`, but we need a different proof for that. -/
lemma lt_sub_iff_left : a < b - c ↔ c + a < b :=
contravariant.add_le_cancellable.lt_sub_iff_left

/-- This lemma also holds for `ennreal`, but we need a different proof for that. -/
lemma sub_lt_sub_iff_right' (h : c ≤ a) : a - c < b - c ↔ a < b :=
contravariant.add_le_cancellable.sub_lt_sub_iff_right h

lemma lt_sub_iff_lt_sub : a < b - c ↔ c < b - a :=
contravariant.add_le_cancellable.lt_sub_iff_lt_sub contravariant.add_le_cancellable

lemma sub_lt_self' (h₁ : 0 < a) (h₂ : 0 < b) : a - b < a :=
contravariant.add_le_cancellable.sub_lt_self contravariant.add_le_cancellable h₁ h₂

lemma sub_lt_self_iff' : a - b < a ↔ 0 < a ∧ 0 < b :=
contravariant.add_le_cancellable.sub_lt_self_iff contravariant.add_le_cancellable

/-- See `lt_sub_iff_left_of_le_of_le` for a weaker statement in a partial order. -/
lemma sub_lt_sub_iff_left_of_le (h : b ≤ a) : a - b < a - c ↔ c < b :=
contravariant.add_le_cancellable.sub_lt_sub_iff_left_of_le contravariant.add_le_cancellable h

end contra

/-! Lemmas about `max` and `min`. -/

lemma sub_add_eq_max : a - b + b = max a b :=
begin
  cases le_total a b with h h,
  { rw [max_eq_right h, sub_eq_zero_iff_le.mpr h, zero_add] },
  { rw [max_eq_left h, sub_add_cancel_of_le h] }
end

lemma add_sub_eq_max : a + (b - a) = max a b :=
by rw [add_comm, max_comm, sub_add_eq_max]

lemma sub_min : a - min a b = a - b :=
begin
  cases le_total a b with h h,
  { rw [min_eq_left h, sub_self', sub_eq_zero_iff_le.mpr h] },
  { rw [min_eq_right h] }
end

lemma sub_add_min : a - b + min a b = a :=
by { rw [← sub_min, sub_add_cancel_of_le], apply min_le_left }

end canonically_linear_ordered_add_monoid
