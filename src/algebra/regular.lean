/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.group

/-!
# Regular elements

We introduce left-regular, right-regular and regular elements.

By definition, a regular element in a commutative ring is a non-zero divisor.
Lemma `is_regular_of_integral_domain` shows that every non-zero element of an integral domain
is regular.

The final goal is to develop part of the API to prove, eventually, results about non-zero-divisors.
-/
variables {R : Type*}

/-- A left-regular element is an element `c` such that multiplication on the left by `c`
is injective on the left. -/
def is_left_regular [has_mul R] (c : R) := function.injective ((*) c)

/-- A right-regular element is an element `c` such that multiplication on the right by `c`
is injective on the right. -/
def is_right_regular [has_mul R] (c : R) := function.injective (* c)

/-- A regular element is an element `c` such that multiplication by `c` both on the left and
on the right is injective. -/
structure is_regular [has_mul R] (c : R) : Prop :=
(left : is_left_regular c)
(right : is_right_regular c)

namespace is_regular

variables [monoid R]

/-- An element admitting a right inverse is right-regular. -/
lemma right_of_mul_eq_one {a ai : R} (h : a * ai = 1) : is_right_regular a :=
begin
  intros b c bc,
  rw [← mul_one b, ← mul_one c, ← h, ← mul_assoc, ← mul_assoc],
  exact congr_fun (congr_arg has_mul.mul bc) ai,
end

/-- An element admitting a left inverse is left-regular. -/
lemma left_of_mul_eq_one {a ai : R} (h : ai * a = 1) : is_left_regular a :=
begin
  intros b c bc,
  rw [← one_mul b, ← one_mul c, ← h, mul_assoc, mul_assoc],
  exact congr_arg (has_mul.mul ai) bc,
end

/-- An element admitting a left and a right inverse is regular. -/
lemma unit.is_regular (a : units R) : is_regular (a : R) :=
⟨left_of_mul_eq_one a.inv_mul,  right_of_mul_eq_one a.mul_inv⟩

/--  Elements of a left cancel semigroup are left regular. -/
lemma is_left_regular_of_left_cancel_semigroup {G : Type*} [left_cancel_semigroup G] (g : G) :
  is_left_regular g :=
mul_right_injective g

/--  Elements of a right cancel semigroup are right regular. -/
lemma is_right_regular_of_right_cancel_semigroup {G : Type*} [right_cancel_semigroup G] (g : G) :
  is_right_regular g :=
mul_left_injective g

/--  Elements of a cancel monoid are regular.  Cancel semigroups do not appear to exist. -/
lemma is_regular_of_cancel_monoid {G : Type*} [cancel_monoid G] (g : G) :
  is_regular g :=
⟨mul_right_injective g, mul_left_injective g⟩

/--  Non-zero elements of an integral domain are regular. -/
lemma is_regular_of_cancel_monoid_with_zero {D : Type*} [cancel_monoid_with_zero D] {a : D}
 (a0 : a ≠ 0) :
  is_regular a :=
⟨λ b c, (mul_right_inj' a0).mp, λ b c, (mul_left_inj' a0).mp⟩

end is_regular

open is_regular

/-- A unit in a monoid is regular. -/
lemma is_unit.is_regular [monoid R] {a : R} : is_unit a → is_regular a :=
begin
  rintros ⟨⟨a, b, ab, ba⟩, rfl⟩,
  exact unit.is_regular _,
end
