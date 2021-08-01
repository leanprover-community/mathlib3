/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import algebra.ordered_monoid
/-!
# Ordered Subtraction

This file proves lemmas relating subtraction with an order.
The subtraction discussed here could both be normal subtraction in an additive group or truncated
subtraction on a canonically ordered monoid (`ℕ`, `multiset`, `enat`, `ennreal`, ...)

## Implementation details

Many results about this subtraction are primed,
to not conflict with similar lemmas about ordered groups.

TODO: maybe we should make a multiplicative version of this, so that we can replace lemmas about
`ordered_[add_]comm_group` about subtraction with these.

## Remark

When thinking about this operation, some general examples are
* `dfinsupp` for non-linearly ordered examples
* if `α` is linearly ordered and `β : α → Type*` is a family of ordered add_comm_monoids,then
  `Σ i : α, β i`, ordered lexicographically, with addition given by
  - `x + y = max x y` if `x.1 ≠ y.1`
  - `x + y = ⟨x.1, x.2 + y.2⟩` if `x.1 = y.1`.

-/

/-- `has_ordered_sub α` means that `α` has a subtraction characterized by `a - b ≤ c ↔ a ≤ b + c`.

This is satisfied both by the subtraction in additive ordered groups and by truncated subtraction
in canonically ordered monoids.
-/

class has_ordered_sub (α : Type*) [preorder α] [has_add α] [has_sub α] :=
(sub_le_iff_right : ∀ a b c : α, a - b ≤ c ↔ a ≤ c + b)

variables {α : Type*}

section ordered_add_comm_monoid
variables {a b c d : α} [partial_order α] [add_comm_monoid α] [has_sub α] [has_ordered_sub α]

lemma sub_le_iff_right : a - b ≤ c ↔ a ≤ c + b :=
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

lemma sub_le_of_sub_le (h : a - b ≤ c) : a - c ≤ b :=
by { rw [sub_le_iff_left] at h ⊢, rwa [add_comm] }

lemma sub_le_iff_sub_le : a - b ≤ c ↔ a - c ≤ b :=
⟨sub_le_of_sub_le, sub_le_of_sub_le⟩

lemma sub_sub' (b a c : α) : b - a - c = b - (a + c) :=
begin
  apply le_antisymm,
  { rw [sub_le_iff_left, sub_le_iff_left, ← add_assoc, ← sub_le_iff_left] },
  { rw [sub_le_iff_left, add_assoc, ← sub_le_iff_left, ← sub_le_iff_left] }
end

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

/-- See `add_sub_assoc_of_le` for the equality. -/
lemma add_sub_le_assoc : a + b - c ≤ a + (b - c) :=
by { rw [sub_le_iff_left, add_left_comm], exact add_le_add_left le_add_sub a }

end cov

/--
An element `a : α` is `regular` (name subject to change) if `x ↦ a + x` is order-reflecting.
We will make a separate version of lemmas that require `[contravariant_class α α (+) (≤)]` with
`regular` assumptions instead. These can then be easily instantiated to specific types, like
`ennreal`, where we can replace the assumption `regular x` by `x ≠ ∞`.
These lemmas are named with `_of_reg` appended to the name;
removing `_of_reg` (and potentially adding a prime) gives the lemma for the contravariant case.
-/
def regular {α} [has_le α] [has_add α] (a : α) : Prop :=
∀ ⦃x y⦄, a + x ≤ a + y → x ≤ y

lemma le_add_sub_of_reg (hb : regular b) : a ≤ b + a - b :=
hb le_add_sub

lemma sub_eq_of_eq_add_of_reg (hb : regular b) (h : a = b + c) : a - b = c :=
le_antisymm (sub_le_iff_left.mpr h.le) $
  by { rw h, exact le_add_sub_of_reg hb }

lemma eq_sub_of_add_eq_of_reg (hc : regular c) (h : a + c = b) : a = b - c :=
(sub_eq_of_eq_add_of_reg hc $ by rw [add_comm, h]).symm

@[simp]
lemma add_sub_cancel_right_of_reg (hb : regular b) : a + b - b = a :=
sub_eq_of_eq_add_of_reg hb $ by rw [add_comm]

@[simp]
lemma add_sub_cancel_left_of_reg (ha : regular a) : a + b - a = b :=
sub_eq_of_eq_add_of_reg ha rfl

lemma le_sub_of_add_le_left_of_reg (ha : regular a) (h : a + b ≤ c) : b ≤ c - a :=
ha $ h.trans le_add_sub

lemma le_sub_of_add_le_right_of_reg (hb : regular b) (h : a + b ≤ c) : a ≤ c - b :=
le_sub_of_add_le_left_of_reg hb $ by rwa [add_comm]

lemma lt_add_of_sub_lt_left_of_reg (hb : regular b) (h : a - b < c) : a < b + c :=
begin
  rw [lt_iff_le_and_ne, ← sub_le_iff_left],
  refine ⟨h.le, _⟩,
  rintro rfl,
  simpa [hb] using h,
end

lemma lt_add_of_sub_lt_right_of_reg (hc : regular c) (h : a - c < b) : a < b + c :=
begin
  rw [lt_iff_le_and_ne, ← sub_le_iff_right],
  refine ⟨h.le, _⟩,
  rintro rfl,
  simpa [hc] using h,
end

section contra
variable [contravariant_class α α (+) (≤)]

lemma contravariant.regular : regular a :=
λ x y, le_of_add_le_add_left

lemma le_add_sub' : a ≤ b + a - b :=
le_add_sub_of_reg contravariant.regular

lemma sub_eq_of_eq_add'' (h : a = b + c) : a - b = c :=
sub_eq_of_eq_add_of_reg contravariant.regular h

lemma eq_sub_of_add_eq'' (h : a + c = b) : a = b - c :=
eq_sub_of_add_eq_of_reg contravariant.regular h

@[simp]
lemma add_sub_cancel_right : a + b - b = a :=
add_sub_cancel_right_of_reg contravariant.regular

@[simp]
lemma add_sub_cancel_left : a + b - a = b :=
add_sub_cancel_left_of_reg contravariant.regular

lemma le_sub_of_add_le_left' (h : a + b ≤ c) : b ≤ c - a :=
le_sub_of_add_le_left_of_reg contravariant.regular h

lemma le_sub_of_add_le_right' (h : a + b ≤ c) : a ≤ c - b :=
le_sub_of_add_le_right_of_reg contravariant.regular h

lemma lt_add_of_sub_lt_left' (h : a - b < c) : a < b + c :=
lt_add_of_sub_lt_left_of_reg contravariant.regular h

lemma lt_add_of_sub_lt_right' (h : a - c < b) : a < b + c :=
lt_add_of_sub_lt_right_of_reg contravariant.regular h

-- lemma sub_lt_sub' (hab : a < b) (hcd : c < d) : a - d < b - c :=

-- lemma sub_lt_sub_of_le_of_lt' (hab : a ≤ b) (hcd : c < d) : a - d < b - c :=

-- lemma sub_lt_sub_of_lt_of_le' (hab : a < b) (hcd : c ≤ d) : a - d < b - c :=

-- lemma le_sub : a ≤ b - c ↔ c ≤ b - a :=

-- lemma sub_lt : a - b < c ↔ a - c < b :=

-- lemma F : a < b - c ↔ c < b - a :=
-- lt_sub_iff_add_lt'.trans lt_sub_iff_add_lt.symm

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

section linear_order
variables {a b c d : α} [linear_order α] [add_comm_monoid α] [has_sub α] [has_ordered_sub α]

lemma lt_of_sub_lt_sub_right : a - c < b - c → a < b :=
lt_imp_lt_of_le_imp_le (λ h, sub_le_sub_right' h c)

section cov
variable [covariant_class α α (+) (≤)]

lemma lt_of_sub_lt_sub_left : a - b < a - c → c < b :=
lt_imp_lt_of_le_imp_le (λ h, sub_le_sub_left' h a)

end cov

end linear_order

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

lemma sub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b :=
by rw [← nonpos_iff_eq_zero, sub_le_iff_left, add_zero]

@[simp] lemma sub_self' : a - a = 0 :=
sub_eq_zero_iff_le.mpr le_rfl

lemma sub_le_self' : a - b ≤ a :=
sub_le_iff_left.mpr $ le_add_left le_rfl

@[simp] lemma sub_zero' : a - 0 = a :=
le_antisymm sub_le_self' $ le_add_sub.trans_eq $ zero_add _

lemma sub_le_sub_iff_right (h : c ≤ b) : a - c ≤ b - c ↔ a ≤ b :=
by rw [sub_le_iff_right, sub_add_cancel_of_le h]

lemma sub_self_add (a b : α) : a - (a + b) = 0 :=
by { rw [sub_eq_zero_iff_le], apply self_le_add_right }

lemma sub_cancel (h₁ : a ≤ b) (h₂ : a ≤ c) (h₃ : b - a = c - a) : b = c :=
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



-- lemma sub_lt_sub_iff_left (H : b ≤ a) : a - b < a - c ↔ c < b :=
-- lt_iff_lt_of_le_iff_le (sub_le_sub_iff_left H)

-- lemma sub_le_iff : a - b ≤ c ↔ a - c ≤ b :=
-- sub_le_iff_left_le_add.trans sub_le_iff_right_le_add.symm

-- lemma sub_lt_iff (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < c ↔ a - c < b :=
-- (sub_lt_iff_left_lt_add h₁).trans (sub_lt_iff_right_lt_add h₂).symm

lemma le_sub_iff_left_of_reg (ha : regular a) (h : a ≤ c) : b ≤ c - a ↔ a + b ≤ c :=
⟨λ h2, (add_le_add_left h2 a).trans_eq $ add_sub_cancel_of_le h, le_sub_of_add_le_left_of_reg ha⟩

lemma le_sub_iff_right_of_reg (ha : regular a) (h : a ≤ c) : b ≤ c - a ↔ b + a ≤ c :=
by { rw [add_comm], exact le_sub_iff_left_of_reg ha h }

lemma eq_sub_iff_add_eq_of_le_of_reg (hc : regular c) (h : c ≤ b) : a = b - c ↔ a + c = b :=
begin
  split,
  { rintro rfl, exact sub_add_cancel_of_le h },
  { rintro rfl, exact (add_sub_cancel_right_of_reg hc).symm }
end

lemma sub_eq_iff_eq_add_of_le_of_reg (hb : regular b) (h : b ≤ a) : a - b = c ↔ a = c + b :=
by rw [eq_comm, eq_sub_iff_add_eq_of_le_of_reg hb h, eq_comm]

lemma add_sub_assoc_of_le_of_reg (hc : regular c) (h : c ≤ b) (a : α) : a + b - c = a + (b - c) :=
by conv_lhs { rw [← add_sub_cancel_of_le h, add_comm c, ← add_assoc,
  add_sub_cancel_right_of_reg hc] }

lemma sub_add_eq_add_sub_of_reg (hb : regular b) (h : b ≤ a) : a - b + c = a + c - b :=
by rw [add_comm a, add_sub_assoc_of_le_of_reg hb h, add_comm]

lemma sub_sub_assoc_of_reg (hreg : regular (b - c)) (h₁ : b ≤ a) (h₂ : c ≤ b) :
  a - (b - c) = a - b + c :=
by rw [sub_eq_iff_eq_add_of_le_of_reg hreg (sub_le_self'.trans h₁), add_assoc,
  add_sub_cancel_of_le h₂, sub_add_cancel_of_le h₁]

lemma sub_lt_iff_left_of_reg (hb : regular b) (hba : b ≤ a) : a - b < c ↔ a < b + c :=
begin
  refine ⟨lt_add_of_sub_lt_left_of_reg hb, _⟩,
  intro h, refine (sub_le_iff_left.mpr h.le).lt_of_ne _,
  rintro rfl, exact h.ne' (add_sub_cancel_of_le hba)
end

lemma sub_lt_iff_right_of_reg (hb : regular b) (hba : b ≤ a) : a - b < c ↔ a < c + b :=
by { rw [add_comm], exact sub_lt_iff_left_of_reg hb hba }

lemma sub_le_sub_iff_left_of_reg (ha : regular a) (hc : regular c) (h : c ≤ a) :
  a - b ≤ a - c ↔ c ≤ b :=
begin
  refine ⟨_, λ h, sub_le_sub_left' h a⟩,
  rw [sub_le_iff_left, ← add_sub_assoc_of_le_of_reg hc h,
    le_sub_iff_right_of_reg hc (h.trans le_add_self), add_comm b],
  apply ha,
end

@[simp] lemma add_sub_sub_cancel_of_reg (hreg : regular (a - c)) (h : c ≤ a) :
  (a + b) - (a - c) = b + c :=
(sub_eq_iff_eq_add_of_le_of_reg hreg $ sub_le_self'.trans le_self_add).mpr $
  by rw [add_assoc, add_sub_cancel_of_le h, add_comm]

section contra
variable [contravariant_class α α (+) (≤)]

lemma le_sub_iff_left (h : a ≤ c) : b ≤ c - a ↔ a + b ≤ c :=
le_sub_iff_left_of_reg contravariant.regular h

lemma le_sub_iff_right (h : a ≤ c) : b ≤ c - a ↔ b + a ≤ c :=
le_sub_iff_right_of_reg contravariant.regular h

lemma eq_sub_iff_add_eq_of_le (h : c ≤ b) : a = b - c ↔ a + c = b :=
eq_sub_iff_add_eq_of_le_of_reg contravariant.regular h

lemma sub_eq_iff_eq_add_of_le (h : b ≤ a) : a - b = c ↔ a = c + b :=
sub_eq_iff_eq_add_of_le_of_reg contravariant.regular h

/-- See `add_sub_le_assoc` for an inequality. -/
lemma add_sub_assoc_of_le (h : c ≤ b) (a : α) : a + b - c = a + (b - c) :=
add_sub_assoc_of_le_of_reg contravariant.regular h a

lemma sub_add_eq_add_sub' (h : b ≤ a) : a - b + c = a + c - b :=
sub_add_eq_add_sub_of_reg contravariant.regular h

lemma sub_sub_assoc (h₁ : b ≤ a) (h₂ : c ≤ b) : a - (b - c) = a - b + c :=
sub_sub_assoc_of_reg contravariant.regular h₁ h₂

lemma sub_lt_iff_left (hbc : b ≤ a) : a - b < c ↔ a < b + c :=
sub_lt_iff_left_of_reg contravariant.regular hbc

lemma sub_lt_iff_right (hbc : b ≤ a) : a - b < c ↔ a < c + b :=
sub_lt_iff_right_of_reg contravariant.regular hbc

lemma sub_le_sub_iff_left (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b :=
sub_le_sub_iff_left_of_reg contravariant.regular contravariant.regular h

@[simp] lemma add_sub_sub_cancel' (h : c ≤ a) : (a + b) - (a - c) = b + c :=
add_sub_sub_cancel_of_reg contravariant.regular h

end contra

section cov_lt
variable [covariant_class α α (+) (<)]

example : a < b ↔ ∃ c > 0, b = a + c :=
begin
  simp_rw [lt_iff_le_and_ne, and_comm, le_iff_exists_add, ← exists_and_distrib_left, exists_prop],
  apply exists_congr, intro c,
  rw [and.congr_left_iff, gt_iff_lt], rintro rfl,
  split,
  { rw [pos_iff_ne_zero], apply mt, rintro rfl, rw [add_zero] },
  { rw [← (self_le_add_right a c).lt_iff_ne], apply lt_add_of_pos_right }
end

end cov_lt

section both
variables [covariant_class α α (+) (<)] [contravariant_class α α (+) (≤)]

/-- This lemma also holds for `ennreal`, but we need a different proof for that. Maybe add as field? -/
lemma lt_sub_of_add_lt_right (h : a + c < b) : a < b - c :=
begin
  rwa [← add_sub_cancel_of_le h.le, add_right_comm, add_sub_cancel_right, lt_add_iff_pos_right],
  exact sub_pos_of_lt' h,
end

lemma lt_sub_of_add_lt_left (h : a + c < b) : c < b - a :=
by { apply lt_sub_of_add_lt_right, rwa add_comm }

-- todo
lemma sub_lt_sub_right_of_le (h : c ≤ a) (h2 : a < b) : a - c < b - c :=
by { apply lt_sub_of_add_lt_left, rwa [add_sub_cancel_of_le h] }

-- todo
lemma lt_of_sub_lt_sub_right_of_le (h : c ≤ a) (h2 : a - c < b - c) : a < b :=
by { rwa [← add_sub_cancel_of_le h], }

end both

end canonically_ordered_add_monoid

section canonically_linear_ordered_add_monoid
variables [canonically_linear_ordered_add_monoid α] [has_sub α] [has_ordered_sub α] {a b c : α}

lemma sub_pos_iff_lt : 0 < a - b ↔ b < a :=
by rw [sub_pos_iff_not_le, not_le]

lemma sub_eq_sub_min (a b : α) : a - b = a - min a b :=
begin
  cases le_total a b with h h,
  { rw [min_eq_left h, sub_self', sub_eq_zero_iff_le.mpr h] },
  { rw [min_eq_right h] },
end

section contra
variable [contravariant_class α α (+) (≤)]

-- todo
instance : covariant_class α α (+) (<) :=
⟨(covariant_lt_iff_contravariant_le α α (+)).mpr contravariant_class.elim⟩

/-- This lemma also holds for `ennreal`, but we need a different proof for that. -/
lemma lt_sub_iff_right : a < b - c ↔ a + c < b :=
⟨lt_imp_lt_of_le_imp_le sub_le_iff_right.mpr, lt_sub_of_add_lt_right⟩

/-- This lemma also holds for `ennreal`, but we need a different proof for that. -/
lemma lt_sub_iff_left : a < b - c ↔ c + a < b :=
⟨lt_imp_lt_of_le_imp_le sub_le_iff_left.mpr, lt_sub_of_add_lt_left⟩

/-- This lemma also holds for `ennreal`, but we need a different proof for that. -/
lemma sub_lt_sub_iff_right (h : c ≤ a) : a - c < b - c ↔ a < b :=
by rw [lt_sub_iff_left, add_sub_cancel_of_le h]

lemma sub_lt_self' (h₁ : 0 < a) (h₂ : 0 < b) : a - b < a :=
begin
  refine sub_le_self'.lt_of_ne _,
  intro h,
  rw [← h, sub_pos_iff_lt] at h₁,
  have := h.ge,
  rw [le_sub_iff_left h₁.le, add_le_iff_nonpos_left] at this,
  exact h₂.not_le this,
end

lemma sub_lt_self_iff : a - b < a ↔ 0 < a ∧ 0 < b :=
begin
  refine ⟨_, λ h, sub_lt_self' h.1 h.2⟩,
  intro h,
  refine ⟨(zero_le _).trans_lt h, (zero_le b).lt_of_ne _⟩,
  rintro rfl,
  rw [sub_zero'] at h,
  exact h.false
end


end contra

end canonically_linear_ordered_add_monoid
