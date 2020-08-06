/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/

import algebra.group_with_zero

/-!
# Divisibility

This file defines the basics of the divisibility relation in the context of `(comm_)` `monoid`s
`(_with_zero)`.

## Main definitions

`monoid.has_dvd`

## Implementation notes

The divisibility relation is defined for all monoids, and as such, depends on the order of
  multiplication if the monoid is not commutative. There are two possible conventions for
  divisibility in the noncommutative context, and this relation follows the convention for ordinals,
  so `a | b` is defined as `∃ c, b = a * c`.

-/

variables {α : Type*}

section monoid

variables [monoid α] {a b c : α}

/-- There are two possible conventions for divisibility, which coincide in a `comm_monoid`.
    This matches the convention for ordinals. -/
@[priority 100]
instance monoid_has_dvd : has_dvd α :=
has_dvd.mk (λ a b, ∃ c, b = a * c)

-- TODO: this used to not have c explicit, but that seems to be important
--       for use with tactics, similar to exist.intro
theorem dvd.intro (c : α) (h : a * c = b) : a ∣ b :=
exists.intro c h^.symm

alias dvd.intro ← dvd_of_mul_right_eq

theorem exists_eq_mul_right_of_dvd (h : a ∣ b) : ∃ c, b = a * c := h

theorem dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : ∀ c, b = a * c → P) : P :=
exists.elim H₁ H₂

@[refl, simp] theorem dvd_refl (a : α) : a ∣ a :=
dvd.intro 1 (by simp)

local attribute [simp] mul_assoc mul_comm mul_left_comm

@[trans] theorem dvd_trans (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
match h₁, h₂ with
| ⟨d, (h₃ : b = a * d)⟩, ⟨e, (h₄ : c = b * e)⟩ :=
  ⟨d * e, show c = a * (d * e), by simp [h₃, h₄]⟩
end

alias dvd_trans ← dvd.trans

@[simp] theorem one_dvd (a : α) : 1 ∣ a := dvd.intro a (by simp)

@[simp] theorem dvd_mul_right (a b : α) : a ∣ a * b := dvd.intro b rfl

theorem dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c :=
dvd.elim h (λ d h', begin rw [h', mul_assoc], apply dvd_mul_right end)

theorem dvd_of_mul_right_dvd (h : a * b ∣ c) : a ∣ c :=
dvd.elim h (begin intros d h₁, rw [h₁, mul_assoc], apply dvd_mul_right end)

end monoid

section comm_monoid

variables [comm_monoid α] {a b c : α}

theorem dvd.intro_left (c : α) (h : c * a = b) : a ∣ b :=
dvd.intro _ (begin rewrite mul_comm at h, apply h end)

alias dvd.intro_left ← dvd_of_mul_left_eq

theorem exists_eq_mul_left_of_dvd (h : a ∣ b) : ∃ c, b = c * a :=
dvd.elim h (assume c, assume H1 : b = a * c, exists.intro c (eq.trans H1 (mul_comm a c)))

theorem dvd.elim_left {P : Prop} (h₁ : a ∣ b) (h₂ : ∀ c, b = c * a → P) : P :=
exists.elim (exists_eq_mul_left_of_dvd h₁) (assume c, assume h₃ : b = c * a, h₂ c h₃)

@[simp] theorem dvd_mul_left (a b : α) : a ∣ b * a := dvd.intro b (mul_comm a b)

theorem dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c * b :=
begin rw mul_comm, exact dvd_mul_of_dvd_left h _ end

local attribute [simp] mul_assoc mul_comm mul_left_comm

theorem mul_dvd_mul : ∀ {a b c d : α}, a ∣ b → c ∣ d → a * c ∣ b * d
| a ._ c ._ ⟨e, rfl⟩ ⟨f, rfl⟩ := ⟨e * f, by simp⟩

theorem mul_dvd_mul_left (a : α) {b c : α} (h : b ∣ c) : a * b ∣ a * c :=
mul_dvd_mul (dvd_refl a) h

theorem mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c :=
mul_dvd_mul h (dvd_refl c)

theorem dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c :=
dvd.elim h (λ d ceq, dvd.intro (a * d) (by simp [ceq]))

end comm_monoid

section monoid_with_zero

variables [monoid_with_zero α] {a : α}

theorem eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0 :=
dvd.elim h (assume c, assume H' : a = 0 * c, eq.trans H' (zero_mul c))

/-- Given an element a of a commutative monoid with zero, there exists another element whose product
    with zero equals a iff a equals zero. -/
@[simp] lemma zero_dvd_iff : 0 ∣ a ↔ a = 0 :=
⟨eq_zero_of_zero_dvd, λ h, by rw h⟩

@[simp] theorem dvd_zero (a : α) : a ∣ 0 := dvd.intro 0 (by simp)

end monoid_with_zero

/-- Given two elements b, c of an integral domain and a nonzero element a, a*b divides a*c iff
  b divides c. -/
theorem mul_dvd_mul_iff_left [cancel_monoid_with_zero α] {a b c : α}
  (ha : a ≠ 0) : a * b ∣ a * c ↔ b ∣ c :=
exists_congr $ λ d, by rw [mul_assoc, mul_right_inj' ha]

/-!
### Units in various monoids
-/

namespace units

section monoid
variables [monoid α] (a b : α) (u : units α)

/-- Elements of the unit group of a monoid represented as elements of the monoid
    divide any element of the monoid. -/
@[simp] lemma coe_dvd : ↑u ∣ a := ⟨↑u⁻¹ * a, by simp⟩

/-- In a monoid, an element `a` divides an element `b` iff `a` divides all
    associates of `b`. -/
@[simp] lemma dvd_coe_mul : a ∣ b * u ↔ a ∣ b :=
iff.intro
  (assume ⟨c, eq⟩, ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← eq, units.mul_inv_cancel_right]⟩)
  (assume ⟨c, eq⟩, eq.symm ▸ dvd_mul_of_dvd_left (dvd_mul_right _ _) _)

/-- An element of a monoid divides a unit iff the element divides one. -/
@[simp] lemma dvd_coe : a ∣ ↑u ↔ a ∣ 1 :=
suffices a ∣ 1 * ↑u ↔ a ∣ 1, by simpa,
dvd_coe_mul _ _ _

end monoid

/-- In a monoid, an element a divides an element b iff all associates of a divide b.-/
@[simp] lemma coe_mul_dvd [comm_monoid α] (a b : α) (u : units α) : a * u ∣ b ↔ a ∣ b :=
iff.intro
  (assume ⟨c, eq⟩, ⟨c * ↑u, eq.symm ▸ by ac_refl⟩)
  (assume h, suffices a * ↑u ∣ b * 1, by simpa, mul_dvd_mul h (coe_dvd _ _))

end units

namespace is_unit

lemma mul_right_dvd_of_dvd [monoid α]
  {a b c : α} (hb : is_unit b) (h : a ∣ c) : a * b ∣ c :=
begin
  rcases hb with ⟨b, rfl⟩,
  rcases h with ⟨c', rfl⟩,
  use (b⁻¹ : units α) * c',
  rw [mul_assoc, units.mul_inv_cancel_left]
end

lemma mul_left_dvd_of_dvd [comm_monoid α]
  {a b c : α} (hb : is_unit b) (h : a ∣ c) : b * a ∣ c :=
begin
  rcases hb with ⟨b, rfl⟩,
  rcases h with ⟨c', rfl⟩,
  use (b⁻¹ : units α) * c',
  rw [mul_comm (b : α) a, mul_assoc, units.mul_inv_cancel_left]
end

end is_unit
