/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
import algebra.divisibility.basic
import algebra.group.units

/-!
# Lemmas about divisibility and units

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}

namespace units

section monoid
variables [monoid α] {a b : α} {u : αˣ}

/-- Elements of the unit group of a monoid represented as elements of the monoid
    divide any element of the monoid. -/
lemma coe_dvd : ↑u ∣ a := ⟨↑u⁻¹ * a, by simp⟩

/-- In a monoid, an element `a` divides an element `b` iff `a` divides all
    associates of `b`. -/
lemma dvd_mul_right : a ∣ b * u ↔ a ∣ b :=
iff.intro
  (assume ⟨c, eq⟩, ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← eq, units.mul_inv_cancel_right]⟩)
  (assume ⟨c, eq⟩, eq.symm ▸ (dvd_mul_right _ _).mul_right _)

/-- In a monoid, an element `a` divides an element `b` iff all associates of `a` divide `b`. -/
lemma mul_right_dvd : a * u ∣ b ↔ a ∣ b :=
iff.intro
  (λ ⟨c, eq⟩, ⟨↑u * c, eq.trans (mul_assoc _ _ _)⟩)
  (λ h, dvd_trans (dvd.intro ↑u⁻¹ (by rw [mul_assoc, u.mul_inv, mul_one])) h)

end monoid

section comm_monoid
variables [comm_monoid α] {a b : α} {u : αˣ}

/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
    associates of `b`. -/
lemma dvd_mul_left : a ∣ u * b ↔ a ∣ b := by { rw mul_comm, apply dvd_mul_right }

/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.-/
lemma mul_left_dvd : ↑u * a ∣ b ↔ a ∣ b :=
by { rw mul_comm, apply mul_right_dvd }

end comm_monoid

end units

namespace is_unit

section monoid

variables [monoid α] {a b u : α} (hu : is_unit u)
include hu

/-- Units of a monoid divide any element of the monoid. -/
@[simp] lemma dvd : u ∣ a := by { rcases hu with ⟨u, rfl⟩, apply units.coe_dvd, }

@[simp] lemma dvd_mul_right : a ∣ b * u ↔ a ∣ b :=
by { rcases hu with ⟨u, rfl⟩, apply units.dvd_mul_right, }

/-- In a monoid, an element a divides an element b iff all associates of `a` divide `b`.-/
@[simp] lemma mul_right_dvd : a * u ∣ b ↔ a ∣ b :=
by { rcases hu with ⟨u, rfl⟩, apply units.mul_right_dvd, }

end monoid

section comm_monoid
variables [comm_monoid α] (a b u : α) (hu : is_unit u)
include hu

/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
    associates of `b`. -/
@[simp] lemma dvd_mul_left : a ∣ u * b ↔ a ∣ b :=
by { rcases hu with ⟨u, rfl⟩, apply units.dvd_mul_left, }

/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.-/
@[simp] lemma mul_left_dvd : u * a ∣ b ↔ a ∣ b :=
by { rcases hu with ⟨u, rfl⟩, apply units.mul_left_dvd, }

end comm_monoid

end is_unit

section comm_monoid
variables [comm_monoid α]

theorem is_unit_iff_dvd_one {x : α} : is_unit x ↔ x ∣ 1 :=
⟨is_unit.dvd, λ ⟨y, h⟩, ⟨⟨x, y, h.symm, by rw [h, mul_comm]⟩, rfl⟩⟩

theorem is_unit_iff_forall_dvd {x : α} :
  is_unit x ↔ ∀ y, x ∣ y :=
is_unit_iff_dvd_one.trans ⟨λ h y, h.trans (one_dvd _), λ h, h _⟩

theorem is_unit_of_dvd_unit {x y : α}
  (xy : x ∣ y) (hu : is_unit y) : is_unit x :=
is_unit_iff_dvd_one.2 $ xy.trans $ is_unit_iff_dvd_one.1 hu

lemma is_unit_of_dvd_one : ∀a ∣ 1, is_unit (a:α)
| a ⟨b, eq⟩ := ⟨units.mk_of_mul_eq_one a b eq.symm, rfl⟩

lemma not_is_unit_of_not_is_unit_dvd {a b : α} (ha : ¬is_unit a) (hb : a ∣ b) :
  ¬ is_unit b :=
mt (is_unit_of_dvd_unit hb) ha

end comm_monoid
