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

/-- In a semigroup, then the product of left-regular elements is left-regular. -/
lemma is_left_regular.mul [semigroup R] {a b : R}
  (lra : is_left_regular a) (lrb : is_left_regular b) :
  is_left_regular (a * b) :=
λ c d cd, lrb (lra ((mul_assoc a b c).symm.trans (cd.trans (mul_assoc a b d))))

/-- In a semigroup, then the product of right-regular elements is right-regular. -/
lemma is_right_regular.mul [semigroup R] {a b : R}
  (rra : is_right_regular a) (rrb : is_right_regular b) :
  is_right_regular (a * b) :=
λ c d cd, rra (rrb ((mul_assoc c a b).trans (cd.trans (mul_assoc d a b).symm)))

section monoid

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
lemma units.is_regular {G : Type*} [monoid G] (a : units G) : is_regular (a : G) :=
⟨left_of_mul_eq_one a.inv_mul,  right_of_mul_eq_one a.mul_inv⟩

end monoid

section left_or_right_cancel_semigroup

/--  Elements of a left cancel semigroup are left regular. -/
lemma is_left_regular_of_left_cancel_semigroup {G : Type*} [left_cancel_semigroup G] (g : G) :
  is_left_regular g :=
mul_right_injective g

/--  Elements of a right cancel semigroup are right regular. -/
lemma is_right_regular_of_right_cancel_semigroup {G : Type*} [right_cancel_semigroup G] (g : G) :
  is_right_regular g :=
mul_left_injective g

end left_or_right_cancel_semigroup

section cancel_monoid

variables [cancel_monoid R]

/--  Elements of a cancel monoid are regular.  Cancel semigroups do not appear to exist. -/
lemma is_regular_of_cancel_monoid (g : R) : is_regular g :=
⟨mul_right_injective g, mul_left_injective g⟩

end cancel_monoid

section cancel_monoid_with_zero

variables  [cancel_monoid_with_zero R]

/--  Non-zero elements of an integral domain are regular. -/
lemma is_regular_of_cancel_monoid_with_zero {a : R}
 (a0 : a ≠ 0) :
  is_regular a :=
⟨λ b c, (mul_right_inj' a0).mp, λ b c, (mul_left_inj' a0).mp⟩

end cancel_monoid_with_zero

end is_regular

open is_regular

/-- A unit in a monoid is regular. -/
lemma is_unit.is_regular [monoid R] {a : R} : is_unit a → is_regular a :=
begin
  rintros ⟨u, rfl⟩,
  exact units.is_regular u,
end
