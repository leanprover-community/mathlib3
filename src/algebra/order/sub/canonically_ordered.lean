/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import algebra.order.sub.basic
import algebra.order.monoid.with_top

/-! ### Lemmas about subtraction in a canonically ordered monoid. -/

universes u
variables {α : Type u}

section canonically_ordered_add_monoid
variables [canonically_ordered_add_monoid α] [has_sub α] [has_ordered_sub α] {a b c d : α}

lemma add_tsub_cancel_iff_le : a + (b - a) = b ↔ a ≤ b :=
⟨λ h, le_iff_exists_add.mpr ⟨b - a, h.symm⟩, add_tsub_cancel_of_le⟩

lemma tsub_add_cancel_iff_le : b - a + a = b ↔ a ≤ b :=
by { rw [add_comm], exact add_tsub_cancel_iff_le }

@[simp] lemma tsub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b :=
by rw [← nonpos_iff_eq_zero, tsub_le_iff_left, add_zero]

alias tsub_eq_zero_iff_le ↔ _ tsub_eq_zero_of_le

attribute [simp] tsub_eq_zero_of_le

@[simp] lemma tsub_self (a : α) : a - a = 0 := tsub_eq_zero_of_le le_rfl

@[simp] lemma tsub_le_self : a - b ≤ a := tsub_le_iff_left.mpr $ le_add_left le_rfl

@[simp] lemma zero_tsub (a : α) : 0 - a = 0 := tsub_eq_zero_of_le $ zero_le a

lemma tsub_self_add (a b : α) : a - (a + b) = 0 := tsub_eq_zero_of_le $ self_le_add_right _ _

lemma tsub_pos_iff_not_le : 0 < a - b ↔ ¬ a ≤ b :=
by rw [pos_iff_ne_zero, ne.def, tsub_eq_zero_iff_le]

lemma tsub_pos_of_lt (h : a < b) : 0 < b - a := tsub_pos_iff_not_le.mpr h.not_le

lemma tsub_lt_of_lt (h : a < b) : a - c < b := lt_of_le_of_lt tsub_le_self h

namespace add_le_cancellable

protected lemma tsub_le_tsub_iff_left (ha : add_le_cancellable a) (hc : add_le_cancellable c)
  (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b :=
begin
  refine ⟨_, λ h, tsub_le_tsub_left h a⟩,
  rw [tsub_le_iff_left, ← hc.add_tsub_assoc_of_le h, hc.le_tsub_iff_right (h.trans le_add_self),
    add_comm b],
  apply ha,
end

protected lemma tsub_right_inj (ha : add_le_cancellable a) (hb : add_le_cancellable b)
  (hc : add_le_cancellable c) (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c :=
by simp_rw [le_antisymm_iff, ha.tsub_le_tsub_iff_left hb hba, ha.tsub_le_tsub_iff_left hc hca,
  and_comm]

end add_le_cancellable

/-! #### Lemmas where addition is order-reflecting. -/

section contra
variable [contravariant_class α α (+) (≤)]

lemma tsub_le_tsub_iff_left (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b :=
contravariant.add_le_cancellable.tsub_le_tsub_iff_left contravariant.add_le_cancellable h

lemma tsub_right_inj (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c :=
contravariant.add_le_cancellable.tsub_right_inj contravariant.add_le_cancellable
  contravariant.add_le_cancellable hba hca

variables (α)

/-- A `canonically_ordered_add_monoid` with ordered subtraction and order-reflecting addition is
cancellative. This is not an instance at it would form a typeclass loop.

See note [reducible non-instances]. -/
@[reducible]
def canonically_ordered_add_monoid.to_add_cancel_comm_monoid : add_cancel_comm_monoid α :=
{ add_left_cancel := λ a b c h, by simpa only [add_tsub_cancel_left] using congr_arg (λ x, x - a) h,
  ..(by apply_instance : add_comm_monoid α) }

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
  { rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h] },
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

protected lemma tsub_lt_self (ha : add_le_cancellable a) (h₁ : 0 < a) (h₂ : 0 < b) : a - b < a :=
begin
  refine tsub_le_self.lt_of_ne (λ h, _),
  rw [← h, tsub_pos_iff_lt] at h₁,
  exact h₂.not_le (ha.add_le_iff_nonpos_left.1 $ add_le_of_le_tsub_left_of_le h₁.le h.ge),
end

protected lemma tsub_lt_self_iff (ha : add_le_cancellable a) : a - b < a ↔ 0 < a ∧ 0 < b :=
begin
  refine ⟨λ h, ⟨(zero_le _).trans_lt h, (zero_le b).lt_of_ne _⟩, λ h, ha.tsub_lt_self h.1 h.2⟩,
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

lemma tsub_lt_self : 0 < a → 0 < b → a - b < a := contravariant.add_le_cancellable.tsub_lt_self

lemma tsub_lt_self_iff : a - b < a ↔ 0 < a ∧ 0 < b :=
contravariant.add_le_cancellable.tsub_lt_self_iff

/-- See `lt_tsub_iff_left_of_le_of_le` for a weaker statement in a partial order. -/
lemma tsub_lt_tsub_iff_left_of_le (h : b ≤ a) : a - b < a - c ↔ c < b :=
contravariant.add_le_cancellable.tsub_lt_tsub_iff_left_of_le contravariant.add_le_cancellable h

end contra

/-! ### Lemmas about `max` and `min`. -/

lemma tsub_add_eq_max : a - b + b = max a b :=
begin
  cases le_total a b with h h,
  { rw [max_eq_right h, tsub_eq_zero_of_le h, zero_add] },
  { rw [max_eq_left h, tsub_add_cancel_of_le h] }
end

lemma add_tsub_eq_max : a + (b - a) = max a b :=
by rw [add_comm, max_comm, tsub_add_eq_max]

lemma tsub_min : a - min a b = a - b :=
begin
  cases le_total a b with h h,
  { rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h] },
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
