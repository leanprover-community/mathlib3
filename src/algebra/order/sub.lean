/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import algebra.order.monoid
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

lemma add_hom.le_map_tsub [preorder β] [has_add β] [has_sub β] [has_ordered_sub β]
  (f : add_hom α β) (hf : monotone f) (a b : α) :
  f a - f b ≤ f (a - b) :=
by { rw [tsub_le_iff_right, ← f.map_add], exact hf le_tsub_add }

lemma le_mul_tsub {R : Type*} [distrib R] [preorder R] [has_sub R] [has_ordered_sub R]
  [covariant_class R R (*) (≤)] {a b c : R} :
  a * b - a * c ≤ a * (b - c) :=
(add_hom.mul_left a).le_map_tsub (monotone_id.const_mul' a) _ _

lemma le_tsub_mul {R : Type*} [comm_semiring R] [preorder R] [has_sub R] [has_ordered_sub R]
  [covariant_class R R (*) (≤)] {a b c : R} :
  a * c - b * c ≤ (a - b) * c :=
by simpa only [mul_comm _ c] using le_mul_tsub

end has_add

/-- An order isomorphism between types with ordered subtraction preserves subtraction provided that
it preserves addition. -/
lemma order_iso.map_tsub {M N : Type*} [preorder M] [has_add M] [has_sub M] [has_ordered_sub M]
  [partial_order N] [has_add N] [has_sub N] [has_ordered_sub N] (e : M ≃o N)
  (h_add : ∀ a b, e (a + b) = e a + e b) (a b : M) :
  e (a - b) = e a - e b :=
begin
  set e_add : M ≃+ N := { map_add' := h_add, .. e },
  refine le_antisymm _ (e_add.to_add_hom.le_map_tsub e.monotone a b),
  suffices : e (e.symm (e a) - e.symm (e b)) ≤ e (e.symm (e a - e b)), by simpa,
  exact e.monotone (e_add.symm.to_add_hom.le_map_tsub e.symm.monotone _ _)
end

section ordered_add_comm_monoid

section preorder

variables [preorder α] [add_comm_monoid α] [has_sub α] [has_ordered_sub α] {a b c d : α}

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

lemma add_monoid_hom.le_map_tsub [preorder β] [add_comm_monoid β] [has_sub β]
  [has_ordered_sub β] (f : α →+ β) (hf : monotone f) (a b : α) :
  f a - f b ≤ f (a - b) :=
f.to_add_hom.le_map_tsub hf a b

end preorder

variables [partial_order α] [add_comm_monoid α] [has_sub α] [has_ordered_sub α] {a b c d : α}

lemma tsub_tsub (b a c : α) : b - a - c = b - (a + c) :=
begin
  apply le_antisymm,
  { rw [tsub_le_iff_left, tsub_le_iff_left, ← add_assoc, ← tsub_le_iff_left] },
  { rw [tsub_le_iff_left, add_assoc, ← tsub_le_iff_left, ← tsub_le_iff_left] }
end

section cov
variable [covariant_class α α (+) (≤)]

lemma tsub_le_tsub_left (h : a ≤ b) (c : α) : c - b ≤ c - a :=
tsub_le_iff_left.mpr $ le_add_tsub.trans $ add_le_add_right h _

lemma tsub_le_tsub (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
(tsub_le_tsub_right hab _).trans $ tsub_le_tsub_left hcd _

lemma tsub_add_eq_tsub_tsub (a b c : α) : a - (b + c) = a - b - c :=
begin
  refine le_antisymm (tsub_le_iff_left.mpr _)
    (tsub_le_iff_left.mpr $ tsub_le_iff_left.mpr _),
  { rw [add_assoc], refine le_trans le_add_tsub (add_le_add_left le_add_tsub _) },
  { rw [← add_assoc], apply le_add_tsub }
end

lemma tsub_add_eq_tsub_tsub_swap (a b c : α) : a - (b + c) = a - c - b :=
by { rw [add_comm], apply tsub_add_eq_tsub_tsub }

lemma add_le_add_add_tsub : a + b ≤ (a + c) + (b - c) :=
by { rw [add_assoc], exact add_le_add_left le_add_tsub a }

lemma tsub_right_comm : a - b - c = a - c - b :=
by simp_rw [← tsub_add_eq_tsub_tsub, add_comm]

/-- See `add_tsub_assoc_of_le` for the equality. -/
lemma add_tsub_le_assoc : a + b - c ≤ a + (b - c) :=
by { rw [tsub_le_iff_left, add_left_comm], exact add_le_add_left le_add_tsub a }

lemma le_tsub_add_add : a + b ≤ (a - c) + (b + c) :=
by { rw [add_comm a, add_comm (a - c)], exact add_le_add_add_tsub }

lemma tsub_le_tsub_add_tsub : a - c ≤ (a - b) + (b - c) :=
begin
  rw [tsub_le_iff_left, ← add_assoc, add_right_comm],
  refine le_add_tsub.trans (add_le_add_right le_add_tsub _),
end

lemma tsub_tsub_tsub_le_tsub : (c - a) - (c - b) ≤ b - a :=
begin
  rw [tsub_le_iff_left, tsub_le_iff_left, add_left_comm],
  refine le_tsub_add.trans (add_le_add_left le_add_tsub _),
end

end cov

/-! ### Lemmas that assume that an element is `add_le_cancellable`. -/
namespace add_le_cancellable

protected lemma le_add_tsub_swap (hb : add_le_cancellable b) : a ≤ b + a - b :=
hb le_add_tsub

protected lemma le_add_tsub (hb : add_le_cancellable b) : a ≤ a + b - b :=
by { rw [add_comm], exact hb.le_add_tsub_swap }

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

protected lemma le_tsub_of_add_le_left (ha : add_le_cancellable a) (h : a + b ≤ c) : b ≤ c - a :=
ha $ h.trans le_add_tsub

protected lemma le_tsub_of_add_le_right (hb : add_le_cancellable b) (h : a + b ≤ c) : a ≤ c - b :=
hb.le_tsub_of_add_le_left $ by rwa [add_comm]

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

end add_le_cancellable

/-! ### Lemmas where addition is order-reflecting. -/

section contra
variable [contravariant_class α α (+) (≤)]

lemma le_add_tsub_swap : a ≤ b + a - b :=
contravariant.add_le_cancellable.le_add_tsub_swap

lemma le_add_tsub' : a ≤ a + b - b :=
contravariant.add_le_cancellable.le_add_tsub

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

lemma le_tsub_of_add_le_left (h : a + b ≤ c) : b ≤ c - a :=
contravariant.add_le_cancellable.le_tsub_of_add_le_left h

lemma le_tsub_of_add_le_right (h : a + b ≤ c) : a ≤ c - b :=
contravariant.add_le_cancellable.le_tsub_of_add_le_right h

lemma lt_add_of_tsub_lt_left (h : a - b < c) : a < b + c :=
contravariant.add_le_cancellable.lt_add_of_tsub_lt_left h

lemma lt_add_of_tsub_lt_right (h : a - c < b) : a < b + c :=
contravariant.add_le_cancellable.lt_add_of_tsub_lt_right h

end contra

section both
variables [covariant_class α α (+) (≤)] [contravariant_class α α (+) (≤)]

lemma add_tsub_add_eq_tsub_right (a c b : α) : (a + c) - (b + c) = a - b :=
begin
  apply le_antisymm,
  { rw [tsub_le_iff_left, add_right_comm], exact add_le_add_right le_add_tsub c },
  { rw [tsub_le_iff_left, add_comm b],
    apply le_of_add_le_add_right,
    rw [add_assoc],
    exact le_tsub_add }
end

lemma add_tsub_add_eq_tsub_left (a b c : α) : (a + b) - (a + c) = b - c :=
by rw [add_comm a b, add_comm a c, add_tsub_add_eq_tsub_right]

end both

end ordered_add_comm_monoid

/-! ### Lemmas in a linearly ordered monoid. -/
section linear_order
variables {a b c d : α} [linear_order α] [add_comm_monoid α] [has_sub α] [has_ordered_sub α]

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

/-! ### Lemmas in a canonically ordered monoid. -/

section canonically_ordered_add_monoid
variables [canonically_ordered_add_monoid α] [has_sub α] [has_ordered_sub α] {a b c d : α}

@[simp] lemma add_tsub_cancel_of_le (h : a ≤ b) : a + (b - a) = b :=
begin
  refine le_antisymm _ le_add_tsub,
  obtain ⟨c, rfl⟩ := le_iff_exists_add.1 h,
  exact add_le_add_left add_tsub_le_left a,
end

lemma tsub_add_cancel_of_le (h : a ≤ b) : b - a + a = b :=
by { rw [add_comm], exact add_tsub_cancel_of_le h }

lemma add_tsub_cancel_iff_le : a + (b - a) = b ↔ a ≤ b :=
⟨λ h, le_iff_exists_add.mpr ⟨b - a, h.symm⟩, add_tsub_cancel_of_le⟩

lemma tsub_add_cancel_iff_le : b - a + a = b ↔ a ≤ b :=
by { rw [add_comm], exact add_tsub_cancel_iff_le }

lemma add_le_of_le_tsub_right_of_le (h : b ≤ c) (h2 : a ≤ c - b) : a + b ≤ c :=
(add_le_add_right h2 b).trans_eq $ tsub_add_cancel_of_le h

lemma add_le_of_le_tsub_left_of_le (h : a ≤ c) (h2 : b ≤ c - a) : a + b ≤ c :=
(add_le_add_left h2 a).trans_eq $ add_tsub_cancel_of_le h

lemma tsub_le_tsub_iff_right (h : c ≤ b) : a - c ≤ b - c ↔ a ≤ b :=
by rw [tsub_le_iff_right, tsub_add_cancel_of_le h]

lemma tsub_left_inj (h1 : c ≤ a) (h2 : c ≤ b) : a - c = b - c ↔ a = b :=
by simp_rw [le_antisymm_iff, tsub_le_tsub_iff_right h1, tsub_le_tsub_iff_right h2]

/-- See `lt_of_tsub_lt_tsub_right` for a stronger statement in a linear order. -/
lemma lt_of_tsub_lt_tsub_right_of_le (h : c ≤ b) (h2 : a - c < b - c) : a < b :=
by { refine ((tsub_le_tsub_iff_right h).mp h2.le).lt_of_ne _, rintro rfl, exact h2.false }

@[simp] lemma tsub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b :=
by rw [← nonpos_iff_eq_zero, tsub_le_iff_left, add_zero]

/-- One direction of `tsub_eq_zero_iff_le`, as a `@[simp]`-lemma. -/
@[simp] lemma tsub_eq_zero_of_le (h : a ≤ b) : a - b = 0 :=
tsub_eq_zero_iff_le.mpr h

@[simp] lemma tsub_self (a : α) : a - a = 0 :=
tsub_eq_zero_iff_le.mpr le_rfl

@[simp] lemma tsub_le_self : a - b ≤ a :=
tsub_le_iff_left.mpr $ le_add_left le_rfl

@[simp] lemma tsub_zero (a : α) : a - 0 = a :=
le_antisymm tsub_le_self $ le_add_tsub.trans_eq $ zero_add _

@[simp] lemma zero_tsub (a : α) : 0 - a = 0 :=
tsub_eq_zero_iff_le.mpr $ zero_le a

lemma tsub_self_add (a b : α) : a - (a + b) = 0 :=
by { rw [tsub_eq_zero_iff_le], apply self_le_add_right }

lemma tsub_inj_left (h₁ : a ≤ b) (h₂ : a ≤ c) (h₃ : b - a = c - a) : b = c :=
by rw [← tsub_add_cancel_of_le h₁, ← tsub_add_cancel_of_le h₂, h₃]

lemma tsub_pos_iff_not_le : 0 < a - b ↔ ¬ a ≤ b :=
by rw [pos_iff_ne_zero, ne.def, tsub_eq_zero_iff_le]

lemma tsub_pos_of_lt (h : a < b) : 0 < b - a :=
tsub_pos_iff_not_le.mpr h.not_le

lemma tsub_add_tsub_cancel (hab : b ≤ a) (hbc : c ≤ b) : (a - b) + (b - c) = a - c :=
begin
  convert tsub_add_cancel_of_le (tsub_le_tsub_right hab c) using 2,
  rw [tsub_tsub, add_tsub_cancel_of_le hbc],
end

lemma tsub_tsub_tsub_cancel_right (h : c ≤ b) : (a - c) - (b - c) = a - b :=
by rw [tsub_tsub, add_tsub_cancel_of_le h]

/-! ### Lemmas that assume that an element is `add_le_cancellable`. -/

namespace add_le_cancellable
protected lemma eq_tsub_iff_add_eq_of_le (hc : add_le_cancellable c) (h : c ≤ b) :
  a = b - c ↔ a + c = b :=
begin
  split,
  { rintro rfl, exact tsub_add_cancel_of_le h },
  { rintro rfl, exact (hc.add_tsub_cancel_right).symm }
end

protected lemma tsub_eq_iff_eq_add_of_le (hb : add_le_cancellable b) (h : b ≤ a) :
  a - b = c ↔ a = c + b :=
by rw [eq_comm, hb.eq_tsub_iff_add_eq_of_le h, eq_comm]

protected lemma add_tsub_assoc_of_le (hc : add_le_cancellable c) (h : c ≤ b) (a : α) :
  a + b - c = a + (b - c) :=
by conv_lhs { rw [← add_tsub_cancel_of_le h, add_comm c, ← add_assoc,
  hc.add_tsub_cancel_right] }

protected lemma tsub_add_eq_add_tsub (hb : add_le_cancellable b) (h : b ≤ a) :
  a - b + c = a + c - b :=
by rw [add_comm a, hb.add_tsub_assoc_of_le h, add_comm]

protected lemma tsub_tsub_assoc (hbc : add_le_cancellable (b - c)) (h₁ : b ≤ a) (h₂ : c ≤ b) :
  a - (b - c) = a - b + c :=
by rw [hbc.tsub_eq_iff_eq_add_of_le (tsub_le_self.trans h₁), add_assoc,
  add_tsub_cancel_of_le h₂, tsub_add_cancel_of_le h₁]

protected lemma le_tsub_iff_left (ha : add_le_cancellable a) (h : a ≤ c) : b ≤ c - a ↔ a + b ≤ c :=
⟨add_le_of_le_tsub_left_of_le h, ha.le_tsub_of_add_le_left⟩

protected lemma le_tsub_iff_right (ha : add_le_cancellable a) (h : a ≤ c) : b ≤ c - a ↔ b + a ≤ c :=
by { rw [add_comm], exact ha.le_tsub_iff_left h }

protected lemma tsub_lt_iff_left (hb : add_le_cancellable b) (hba : b ≤ a) :
  a - b < c ↔ a < b + c :=
begin
  refine ⟨hb.lt_add_of_tsub_lt_left, _⟩,
  intro h, refine (tsub_le_iff_left.mpr h.le).lt_of_ne _,
  rintro rfl, exact h.ne' (add_tsub_cancel_of_le hba)
end

protected lemma tsub_lt_iff_right (hb : add_le_cancellable b) (hba : b ≤ a) :
  a - b < c ↔ a < c + b :=
by { rw [add_comm], exact hb.tsub_lt_iff_left hba }

protected lemma lt_tsub_of_add_lt_right (hc : add_le_cancellable c) (h : a + c < b) : a < b - c :=
begin
  apply lt_of_le_of_ne,
  { rw [← add_tsub_cancel_of_le h.le, add_right_comm, add_assoc],
    rw [hc.add_tsub_assoc_of_le], refine le_self_add, refine le_add_self },
  { rintro rfl, apply h.not_le, exact le_tsub_add }
end

protected lemma lt_tsub_of_add_lt_left (ha : add_le_cancellable a) (h : a + c < b) : c < b - a :=
by { apply ha.lt_tsub_of_add_lt_right, rwa add_comm }

protected lemma tsub_lt_iff_tsub_lt (hb : add_le_cancellable b) (hc : add_le_cancellable c)
  (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < c ↔ a - c < b :=
by rw [hb.tsub_lt_iff_left h₁, hc.tsub_lt_iff_right h₂]

protected lemma le_tsub_iff_le_tsub (ha : add_le_cancellable a) (hc : add_le_cancellable c)
  (h₁ : a ≤ b) (h₂ : c ≤ b) : a ≤ b - c ↔ c ≤ b - a :=
by rw [ha.le_tsub_iff_left h₁, hc.le_tsub_iff_right h₂]

protected lemma lt_tsub_iff_right_of_le (hc : add_le_cancellable c) (h : c ≤ b) :
  a < b - c ↔ a + c < b :=
begin
  refine ⟨_, hc.lt_tsub_of_add_lt_right⟩,
  intro h2,
  refine (add_le_of_le_tsub_right_of_le h h2.le).lt_of_ne _,
  rintro rfl,
  apply h2.not_le,
  rw [hc.add_tsub_cancel_right]
end

protected lemma lt_tsub_iff_left_of_le (hc : add_le_cancellable c) (h : c ≤ b) :
  a < b - c ↔ c + a < b :=
by { rw [add_comm], exact hc.lt_tsub_iff_right_of_le h }

protected lemma lt_of_tsub_lt_tsub_left_of_le [contravariant_class α α (+) (<)]
  (hb : add_le_cancellable b) (hca : c ≤ a) (h : a - b < a - c) : c < b :=
begin
  conv_lhs at h { rw [← tsub_add_cancel_of_le hca] },
  exact lt_of_add_lt_add_left (hb.lt_add_of_tsub_lt_right h),
end

protected lemma tsub_le_tsub_iff_left (ha : add_le_cancellable a) (hc : add_le_cancellable c)
  (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b :=
begin
  refine ⟨_, λ h, tsub_le_tsub_left h a⟩,
  rw [tsub_le_iff_left, ← hc.add_tsub_assoc_of_le h,
    hc.le_tsub_iff_right (h.trans le_add_self), add_comm b],
  apply ha,
end

protected lemma tsub_right_inj (ha : add_le_cancellable a) (hb : add_le_cancellable b)
  (hc : add_le_cancellable c) (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c :=
by simp_rw [le_antisymm_iff, ha.tsub_le_tsub_iff_left hb hba, ha.tsub_le_tsub_iff_left hc hca,
  and_comm]

protected lemma tsub_lt_tsub_right_of_le (hc : add_le_cancellable c) (h : c ≤ a) (h2 : a < b) :
  a - c < b - c :=
by { apply hc.lt_tsub_of_add_lt_left, rwa [add_tsub_cancel_of_le h] }

protected lemma tsub_inj_right (hab : add_le_cancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a)
  (h₃ : a - b = a - c) : b = c :=
by { rw ← hab.inj, rw [tsub_add_cancel_of_le h₁, h₃, tsub_add_cancel_of_le h₂] }

protected lemma tsub_lt_tsub_iff_left_of_le_of_le [contravariant_class α α (+) (<)]
  (hb : add_le_cancellable b) (hab : add_le_cancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a) :
  a - b < a - c ↔ c < b :=
begin
  refine ⟨hb.lt_of_tsub_lt_tsub_left_of_le h₂, _⟩,
  intro h, refine (tsub_le_tsub_left h.le _).lt_of_ne _,
  rintro h2, exact h.ne' (hab.tsub_inj_right h₁ h₂ h2)
end

@[simp] protected lemma add_tsub_tsub_cancel (hac : add_le_cancellable (a - c)) (h : c ≤ a) :
  (a + b) - (a - c) = b + c :=
(hac.tsub_eq_iff_eq_add_of_le $ tsub_le_self.trans le_self_add).mpr $
  by rw [add_assoc, add_tsub_cancel_of_le h, add_comm]

protected lemma tsub_tsub_cancel_of_le (hba : add_le_cancellable (b - a)) (h : a ≤ b) :
  b - (b - a) = a :=
by rw [hba.tsub_eq_iff_eq_add_of_le tsub_le_self, add_tsub_cancel_of_le h]

end add_le_cancellable

section contra
/-! ### Lemmas where addition is order-reflecting. -/
variable [contravariant_class α α (+) (≤)]

lemma eq_tsub_iff_add_eq_of_le (h : c ≤ b) : a = b - c ↔ a + c = b :=
contravariant.add_le_cancellable.eq_tsub_iff_add_eq_of_le h

lemma tsub_eq_iff_eq_add_of_le (h : b ≤ a) : a - b = c ↔ a = c + b :=
contravariant.add_le_cancellable.tsub_eq_iff_eq_add_of_le h

/-- See `add_tsub_le_assoc` for an inequality. -/
lemma add_tsub_assoc_of_le (h : c ≤ b) (a : α) : a + b - c = a + (b - c) :=
contravariant.add_le_cancellable.add_tsub_assoc_of_le h a

lemma tsub_add_eq_add_tsub (h : b ≤ a) : a - b + c = a + c - b :=
contravariant.add_le_cancellable.tsub_add_eq_add_tsub h

lemma tsub_tsub_assoc (h₁ : b ≤ a) (h₂ : c ≤ b) : a - (b - c) = a - b + c :=
contravariant.add_le_cancellable.tsub_tsub_assoc h₁ h₂

lemma le_tsub_iff_left (h : a ≤ c) : b ≤ c - a ↔ a + b ≤ c :=
contravariant.add_le_cancellable.le_tsub_iff_left h

lemma le_tsub_iff_right (h : a ≤ c) : b ≤ c - a ↔ b + a ≤ c :=
contravariant.add_le_cancellable.le_tsub_iff_right h

lemma tsub_lt_iff_left (hbc : b ≤ a) : a - b < c ↔ a < b + c :=
contravariant.add_le_cancellable.tsub_lt_iff_left hbc

lemma tsub_lt_iff_right (hbc : b ≤ a) : a - b < c ↔ a < c + b :=
contravariant.add_le_cancellable.tsub_lt_iff_right hbc

/-- This lemma (and some of its corollaries also holds for `ennreal`,
  but this proof doesn't work for it.
  Maybe we should add this lemma as field to `has_ordered_sub`? -/
lemma lt_tsub_of_add_lt_right (h : a + c < b) : a < b - c :=
contravariant.add_le_cancellable.lt_tsub_of_add_lt_right h

lemma lt_tsub_of_add_lt_left (h : a + c < b) : c < b - a :=
contravariant.add_le_cancellable.lt_tsub_of_add_lt_left h

lemma tsub_lt_iff_tsub_lt (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < c ↔ a - c < b :=
contravariant.add_le_cancellable.tsub_lt_iff_tsub_lt contravariant.add_le_cancellable h₁ h₂

lemma le_tsub_iff_le_tsub (h₁ : a ≤ b) (h₂ : c ≤ b) : a ≤ b - c ↔ c ≤ b - a :=
contravariant.add_le_cancellable.le_tsub_iff_le_tsub contravariant.add_le_cancellable h₁ h₂

/-- See `lt_tsub_iff_right` for a stronger statement in a linear order. -/
lemma lt_tsub_iff_right_of_le (h : c ≤ b) : a < b - c ↔ a + c < b :=
contravariant.add_le_cancellable.lt_tsub_iff_right_of_le h

/-- See `lt_tsub_iff_left` for a stronger statement in a linear order. -/
lemma lt_tsub_iff_left_of_le (h : c ≤ b) : a < b - c ↔ c + a < b :=
contravariant.add_le_cancellable.lt_tsub_iff_left_of_le h

/-- See `lt_of_tsub_lt_tsub_left` for a stronger statement in a linear order. -/
lemma lt_of_tsub_lt_tsub_left_of_le  [contravariant_class α α (+) (<)]
  (hca : c ≤ a) (h : a - b < a - c) : c < b :=
contravariant.add_le_cancellable.lt_of_tsub_lt_tsub_left_of_le hca h

lemma tsub_le_tsub_iff_left (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b :=
contravariant.add_le_cancellable.tsub_le_tsub_iff_left contravariant.add_le_cancellable h

lemma tsub_right_inj (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c :=
contravariant.add_le_cancellable.tsub_right_inj contravariant.add_le_cancellable
  contravariant.add_le_cancellable hba hca

lemma tsub_lt_tsub_right_of_le (h : c ≤ a) (h2 : a < b) : a - c < b - c :=
contravariant.add_le_cancellable.tsub_lt_tsub_right_of_le h h2

lemma tsub_inj_right (h₁ : b ≤ a) (h₂ : c ≤ a) (h₃ : a - b = a - c) : b = c :=
contravariant.add_le_cancellable.tsub_inj_right h₁ h₂ h₃

/-- See `tsub_lt_tsub_iff_left_of_le` for a stronger statement in a linear order. -/
lemma tsub_lt_tsub_iff_left_of_le_of_le  [contravariant_class α α (+) (<)]
  (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < a - c ↔ c < b :=
contravariant.add_le_cancellable.tsub_lt_tsub_iff_left_of_le_of_le
  contravariant.add_le_cancellable h₁ h₂

@[simp] lemma add_tsub_tsub_cancel (h : c ≤ a) : (a + b) - (a - c) = b + c :=
contravariant.add_le_cancellable.add_tsub_tsub_cancel h

/-- See `tsub_tsub_le` for an inequality. -/
lemma tsub_tsub_cancel_of_le (h : a ≤ b) : b - (b - a) = a :=
contravariant.add_le_cancellable.tsub_tsub_cancel_of_le h

end contra

end canonically_ordered_add_monoid

/-! ### Lemmas in a linearly canonically ordered monoid. -/

section canonically_linear_ordered_add_monoid
variables [canonically_linear_ordered_add_monoid α] [has_sub α] [has_ordered_sub α] {a b c d : α}

@[simp] lemma tsub_pos_iff_lt : 0 < a - b ↔ b < a :=
by rw [tsub_pos_iff_not_le, not_le]

lemma tsub_eq_tsub_min (a b : α) : a - b = a - min a b :=
begin
  cases le_total a b with h h,
  { rw [min_eq_left h, tsub_self, tsub_eq_zero_iff_le.mpr h] },
  { rw [min_eq_right h] },
end

namespace add_le_cancellable

protected lemma lt_tsub_iff_right (hc : add_le_cancellable c) : a < b - c ↔ a + c < b :=
⟨lt_imp_lt_of_le_imp_le tsub_le_iff_right.mpr, hc.lt_tsub_of_add_lt_right⟩

protected lemma lt_tsub_iff_left (hc : add_le_cancellable c) : a < b - c ↔ c + a < b :=
⟨lt_imp_lt_of_le_imp_le tsub_le_iff_left.mpr, hc.lt_tsub_of_add_lt_left⟩

protected lemma tsub_lt_tsub_iff_right (hc : add_le_cancellable c) (h : c ≤ a) :
  a - c < b - c ↔ a < b :=
by rw [hc.lt_tsub_iff_left, add_tsub_cancel_of_le h]

protected lemma tsub_lt_self (ha : add_le_cancellable a) (hb : add_le_cancellable b)
  (h₁ : 0 < a) (h₂ : 0 < b) : a - b < a :=
begin
  refine tsub_le_self.lt_of_ne _,
  intro h,
  rw [← h, tsub_pos_iff_lt] at h₁,
  have := h.ge,
  rw [hb.le_tsub_iff_left h₁.le, ha.add_le_iff_nonpos_left] at this,
  exact h₂.not_le this,
end

protected lemma tsub_lt_self_iff (ha : add_le_cancellable a) (hb : add_le_cancellable b) :
  a - b < a ↔ 0 < a ∧ 0 < b :=
begin
  refine ⟨_, λ h, ha.tsub_lt_self hb h.1 h.2⟩,
  intro h,
  refine ⟨(zero_le _).trans_lt h, (zero_le b).lt_of_ne _⟩,
  rintro rfl,
  rw [tsub_zero] at h,
  exact h.false
end

/-- See `lt_tsub_iff_left_of_le_of_le` for a weaker statement in a partial order. -/
protected lemma tsub_lt_tsub_iff_left_of_le (ha : add_le_cancellable a) (hb : add_le_cancellable b)
  (h : b ≤ a) : a - b < a - c ↔ c < b :=
lt_iff_lt_of_le_iff_le $ ha.tsub_le_tsub_iff_left hb h

end add_le_cancellable

section contra
variable [contravariant_class α α (+) (≤)]

/-- This lemma also holds for `ennreal`, but we need a different proof for that. -/
lemma tsub_lt_tsub_iff_right (h : c ≤ a) : a - c < b - c ↔ a < b :=
contravariant.add_le_cancellable.tsub_lt_tsub_iff_right h

lemma tsub_lt_self (h₁ : 0 < a) (h₂ : 0 < b) : a - b < a :=
contravariant.add_le_cancellable.tsub_lt_self contravariant.add_le_cancellable h₁ h₂

lemma tsub_lt_self_iff : a - b < a ↔ 0 < a ∧ 0 < b :=
contravariant.add_le_cancellable.tsub_lt_self_iff contravariant.add_le_cancellable

/-- See `lt_tsub_iff_left_of_le_of_le` for a weaker statement in a partial order. -/
lemma tsub_lt_tsub_iff_left_of_le (h : b ≤ a) : a - b < a - c ↔ c < b :=
contravariant.add_le_cancellable.tsub_lt_tsub_iff_left_of_le contravariant.add_le_cancellable h

end contra

/-! ### Lemmas about `max` and `min`. -/

lemma tsub_add_eq_max : a - b + b = max a b :=
begin
  cases le_total a b with h h,
  { rw [max_eq_right h, tsub_eq_zero_iff_le.mpr h, zero_add] },
  { rw [max_eq_left h, tsub_add_cancel_of_le h] }
end

lemma add_tsub_eq_max : a + (b - a) = max a b :=
by rw [add_comm, max_comm, tsub_add_eq_max]

lemma tsub_min : a - min a b = a - b :=
begin
  cases le_total a b with h h,
  { rw [min_eq_left h, tsub_self, tsub_eq_zero_iff_le.mpr h] },
  { rw [min_eq_right h] }
end

lemma tsub_add_min : a - b + min a b = a :=
by { rw [← tsub_min, tsub_add_cancel_of_le], apply min_le_left }

end canonically_linear_ordered_add_monoid

namespace with_top

section
variables [has_sub α] [has_zero α]

/-- If `α` has subtraction and `0`, we can extend the subtraction to `with_top α`. -/
protected def sub : Π (a b : with_top α), with_top α
| _       ⊤       := 0
| ⊤       (x : α) := ⊤
| (x : α) (y : α) := (x - y : α)

instance : has_sub (with_top α) :=
⟨with_top.sub⟩

@[simp, norm_cast] lemma coe_sub {a b : α} : (↑(a - b) : with_top α) = ↑a - ↑b := rfl
@[simp] lemma top_sub_coe {a : α} : (⊤ : with_top α) - a = ⊤ := rfl
@[simp] lemma sub_top {a : with_top α} : a - ⊤ = 0 := by { cases a; refl }

end

variables [canonically_ordered_add_monoid α] [has_sub α] [has_ordered_sub α]
instance : has_ordered_sub (with_top α) :=
begin
  constructor,
  rintro x y z,
  induction y using with_top.rec_top_coe, { simp },
  induction x using with_top.rec_top_coe, { simp },
  induction z using with_top.rec_top_coe, { simp },
  norm_cast, exact tsub_le_iff_right
end

end with_top
