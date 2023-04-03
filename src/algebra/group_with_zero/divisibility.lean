/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
import algebra.group_with_zero.basic
import algebra.divisibility.units

/-!
# Divisibility in groups with zero.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Lemmas about divisibility in groups and monoids with zero.

-/

variables {α : Type*}


section semigroup_with_zero

variables [semigroup_with_zero α] {a : α}

theorem eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0 :=
dvd.elim h (λ c H', H'.trans (zero_mul c))

/-- Given an element `a` of a commutative semigroup with zero, there exists another element whose
    product with zero equals `a` iff `a` equals zero. -/
@[simp] lemma zero_dvd_iff : 0 ∣ a ↔ a = 0 :=
⟨eq_zero_of_zero_dvd, λ h, by { rw h, use 0, simp }⟩

@[simp] theorem dvd_zero (a : α) : a ∣ 0 := dvd.intro 0 (by simp)

end semigroup_with_zero

/-- Given two elements `b`, `c` of a `cancel_monoid_with_zero` and a nonzero element `a`,
 `a*b` divides `a*c` iff `b` divides `c`. -/
theorem mul_dvd_mul_iff_left [cancel_monoid_with_zero α] {a b c : α}
  (ha : a ≠ 0) : a * b ∣ a * c ↔ b ∣ c :=
exists_congr $ λ d, by rw [mul_assoc, mul_right_inj' ha]

/-- Given two elements `a`, `b` of a commutative `cancel_monoid_with_zero` and a nonzero
  element `c`, `a*c` divides `b*c` iff `a` divides `b`. -/
theorem mul_dvd_mul_iff_right [cancel_comm_monoid_with_zero α] {a b c : α} (hc : c ≠ 0) :
  a * c ∣ b * c ↔ a ∣ b :=
exists_congr $ λ d, by rw [mul_right_comm, mul_left_inj' hc]

section comm_monoid_with_zero

variable [comm_monoid_with_zero α]

/-- `dvd_not_unit a b` expresses that `a` divides `b` "strictly", i.e. that `b` divided by `a`
is not a unit. -/
def dvd_not_unit (a b : α) : Prop := a ≠ 0 ∧ ∃ x, ¬is_unit x ∧ b = a * x

lemma dvd_not_unit_of_dvd_of_not_dvd {a b : α} (hd : a ∣ b) (hnd : ¬ b ∣ a) :
  dvd_not_unit a b :=
begin
  split,
  { rintro rfl, exact hnd (dvd_zero _) },
  { rcases hd with ⟨c, rfl⟩,
    refine ⟨c, _, rfl⟩,
    rintro ⟨u, rfl⟩,
    simpa using hnd }
end

end comm_monoid_with_zero

lemma dvd_and_not_dvd_iff [cancel_comm_monoid_with_zero α] {x y : α} :
  x ∣ y ∧ ¬y ∣ x ↔ dvd_not_unit x y :=
⟨λ ⟨⟨d, hd⟩, hyx⟩, ⟨λ hx0, by simpa [hx0] using hyx, ⟨d,
    mt is_unit_iff_dvd_one.1 (λ ⟨e, he⟩, hyx ⟨e, by rw [hd, mul_assoc, ← he, mul_one]⟩), hd⟩⟩,
  λ ⟨hx0, d, hdu, hdx⟩, ⟨⟨d, hdx⟩, λ ⟨e, he⟩, hdu (is_unit_of_dvd_one _
    ⟨e, mul_left_cancel₀ hx0 $ by conv {to_lhs, rw [he, hdx]};simp [mul_assoc]⟩)⟩⟩

section monoid_with_zero

variable [monoid_with_zero α]

theorem ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q ≠ 0)
  (h₂ : p ∣ q) : p ≠ 0 :=
begin
  rcases h₂ with ⟨u, rfl⟩,
  exact left_ne_zero_of_mul h₁,
end

end monoid_with_zero
