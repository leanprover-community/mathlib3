/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import algebra.order.monoid.canonical.defs
import algebra.order.sub.defs

/-!
# Lemmas about subtraction in canonically ordered monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}

section has_exists_add_of_le
variables [add_comm_semigroup α] [partial_order α] [has_exists_add_of_le α]
  [covariant_class α α (+) (≤)] [has_sub α] [has_ordered_sub α] {a b c d : α}

@[simp] lemma add_tsub_cancel_of_le (h : a ≤ b) : a + (b - a) = b :=
begin
  refine le_antisymm _ le_add_tsub,
  obtain ⟨c, rfl⟩ := exists_add_of_le h,
  exact add_le_add_left add_tsub_le_left a,
end

lemma tsub_add_cancel_of_le (h : a ≤ b) : b - a + a = b :=
by { rw [add_comm], exact add_tsub_cancel_of_le h }

lemma add_le_of_le_tsub_right_of_le (h : b ≤ c) (h2 : a ≤ c - b) : a + b ≤ c :=
(add_le_add_right h2 b).trans_eq $ tsub_add_cancel_of_le h

lemma add_le_of_le_tsub_left_of_le (h : a ≤ c) (h2 : b ≤ c - a) : a + b ≤ c :=
(add_le_add_left h2 a).trans_eq $ add_tsub_cancel_of_le h

lemma tsub_le_tsub_iff_right (h : c ≤ b) : a - c ≤ b - c ↔ a ≤ b :=
by rw [tsub_le_iff_right, tsub_add_cancel_of_le h]

lemma tsub_left_inj (h1 : c ≤ a) (h2 : c ≤ b) : a - c = b - c ↔ a = b :=
by simp_rw [le_antisymm_iff, tsub_le_tsub_iff_right h1, tsub_le_tsub_iff_right h2]

lemma tsub_inj_left (h₁ : a ≤ b) (h₂ : a ≤ c) : b - a = c - a → b = c := (tsub_left_inj h₁ h₂).1

/-- See `lt_of_tsub_lt_tsub_right` for a stronger statement in a linear order. -/
lemma lt_of_tsub_lt_tsub_right_of_le (h : c ≤ b) (h2 : a - c < b - c) : a < b :=
by { refine ((tsub_le_tsub_iff_right h).mp h2.le).lt_of_ne _, rintro rfl, exact h2.false }

lemma tsub_add_tsub_cancel (hab : b ≤ a) (hcb : c ≤ b) : (a - b) + (b - c) = a - c :=
begin
  convert tsub_add_cancel_of_le (tsub_le_tsub_right hab c) using 2,
  rw [tsub_tsub, add_tsub_cancel_of_le hcb],
end

lemma tsub_tsub_tsub_cancel_right (h : c ≤ b) : (a - c) - (b - c) = a - b :=
by rw [tsub_tsub, add_tsub_cancel_of_le h]

/-! #### Lemmas that assume that an element is `add_le_cancellable`. -/

namespace add_le_cancellable

protected lemma eq_tsub_iff_add_eq_of_le (hc : add_le_cancellable c) (h : c ≤ b) :
  a = b - c ↔ a + c = b :=
⟨by { rintro rfl, exact tsub_add_cancel_of_le h }, hc.eq_tsub_of_add_eq⟩

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
hbc.tsub_eq_of_eq_add $ by rw [add_assoc, add_tsub_cancel_of_le h₂, tsub_add_cancel_of_le h₁]

protected lemma tsub_add_tsub_comm (hb : add_le_cancellable b) (hd : add_le_cancellable d)
  (hba : b ≤ a) (hdc : d ≤ c) : a - b + (c - d) = a + c - (b + d) :=
by rw [hb.tsub_add_eq_add_tsub hba, ←hd.add_tsub_assoc_of_le hdc, tsub_tsub, add_comm d]

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

protected lemma tsub_lt_iff_tsub_lt (hb : add_le_cancellable b) (hc : add_le_cancellable c)
  (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < c ↔ a - c < b :=
by rw [hb.tsub_lt_iff_left h₁, hc.tsub_lt_iff_right h₂]

protected lemma le_tsub_iff_le_tsub (ha : add_le_cancellable a) (hc : add_le_cancellable c)
  (h₁ : a ≤ b) (h₂ : c ≤ b) : a ≤ b - c ↔ c ≤ b - a :=
by rw [ha.le_tsub_iff_left h₁, hc.le_tsub_iff_right h₂]

protected lemma lt_tsub_iff_right_of_le (hc : add_le_cancellable c) (h : c ≤ b) :
  a < b - c ↔ a + c < b :=
begin
  refine ⟨λ h', (add_le_of_le_tsub_right_of_le h h'.le).lt_of_ne _, hc.lt_tsub_of_add_lt_right⟩,
  rintro rfl,
  exact h'.ne' hc.add_tsub_cancel_right,
end

protected lemma lt_tsub_iff_left_of_le (hc : add_le_cancellable c) (h : c ≤ b) :
  a < b - c ↔ c + a < b :=
by { rw [add_comm], exact hc.lt_tsub_iff_right_of_le h }

protected lemma tsub_inj_right (hab : add_le_cancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a)
  (h₃ : a - b = a - c) : b = c :=
by { rw ← hab.inj, rw [tsub_add_cancel_of_le h₁, h₃, tsub_add_cancel_of_le h₂] }

protected lemma lt_of_tsub_lt_tsub_left_of_le [contravariant_class α α (+) (<)]
  (hb : add_le_cancellable b) (hca : c ≤ a) (h : a - b < a - c) : c < b :=
begin
  conv_lhs at h { rw [← tsub_add_cancel_of_le hca] },
  exact lt_of_add_lt_add_left (hb.lt_add_of_tsub_lt_right h),
end

protected lemma tsub_lt_tsub_left_of_le (hab : add_le_cancellable (a - b)) (h₁ : b ≤ a)
  (h : c < b) : a - b < a - c :=
(tsub_le_tsub_left h.le _).lt_of_ne $ λ h', h.ne' $ hab.tsub_inj_right h₁ (h.le.trans h₁) h'

protected lemma tsub_lt_tsub_right_of_le (hc : add_le_cancellable c) (h : c ≤ a) (h2 : a < b) :
  a - c < b - c :=
by { apply hc.lt_tsub_of_add_lt_left, rwa [add_tsub_cancel_of_le h] }

protected lemma tsub_lt_tsub_iff_left_of_le_of_le [contravariant_class α α (+) (<)]
  (hb : add_le_cancellable b) (hab : add_le_cancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a) :
  a - b < a - c ↔ c < b :=
⟨hb.lt_of_tsub_lt_tsub_left_of_le h₂, hab.tsub_lt_tsub_left_of_le h₁⟩

@[simp] protected lemma add_tsub_tsub_cancel (hac : add_le_cancellable (a - c)) (h : c ≤ a) :
  (a + b) - (a - c) = b + c :=
hac.tsub_eq_of_eq_add $ by rw [add_assoc, add_tsub_cancel_of_le h, add_comm]

protected lemma tsub_tsub_cancel_of_le (hba : add_le_cancellable (b - a)) (h : a ≤ b) :
  b - (b - a) = a :=
hba.tsub_eq_of_eq_add (add_tsub_cancel_of_le h).symm

protected lemma tsub_tsub_tsub_cancel_left (hab : add_le_cancellable (a - b)) (h : b ≤ a) :
  a - c - (a - b) = b - c :=
by rw [tsub_right_comm, hab.tsub_tsub_cancel_of_le h]

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

lemma tsub_add_tsub_comm (hba : b ≤ a) (hdc : d ≤ c) : a - b + (c - d) = a + c - (b + d) :=
contravariant.add_le_cancellable.tsub_add_tsub_comm contravariant.add_le_cancellable hba hdc

lemma le_tsub_iff_left (h : a ≤ c) : b ≤ c - a ↔ a + b ≤ c :=
contravariant.add_le_cancellable.le_tsub_iff_left h

lemma le_tsub_iff_right (h : a ≤ c) : b ≤ c - a ↔ b + a ≤ c :=
contravariant.add_le_cancellable.le_tsub_iff_right h

lemma tsub_lt_iff_left (hbc : b ≤ a) : a - b < c ↔ a < b + c :=
contravariant.add_le_cancellable.tsub_lt_iff_left hbc

lemma tsub_lt_iff_right (hbc : b ≤ a) : a - b < c ↔ a < c + b :=
contravariant.add_le_cancellable.tsub_lt_iff_right hbc

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

lemma tsub_lt_tsub_left_of_le : b ≤ a → c < b → a - b < a - c :=
contravariant.add_le_cancellable.tsub_lt_tsub_left_of_le

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

lemma tsub_tsub_tsub_cancel_left (h : b ≤ a) : a - c - (a - b) = b - c :=
contravariant.add_le_cancellable.tsub_tsub_tsub_cancel_left h

end contra
end has_exists_add_of_le

/-! ### Lemmas in a canonically ordered monoid. -/

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
