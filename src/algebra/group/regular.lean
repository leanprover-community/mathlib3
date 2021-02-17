/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.group

/-!
# Regular elements

We introduce left-regular, right-regular and regular elements.  The final goal is to develop
part of the API to prove, eventually, results about non-zero-divisors.

-/
variables {R : Type*}

/-- A regular element is an element `c` such that multiplication by `c` both on the left and
on the right is injective. -/
structure is_regular [has_mul R] (c : R) : Prop :=
( mul_left_inj : ∀ a b : R, c * a = c * b → a = b)
( mul_right_inj : ∀ a b : R, a * c = b * c → a = b)

namespace is_regular

/-- A left-regular element is an element `c` such that multiplication on the left by `c`
is injective on the left. -/
structure left [has_mul R] (c : R) : Prop :=
( mul_left_inj : ∀ a b : R, c * a = c * b → a = b)

/-- A right-regular element is an element `c` such that multiplication on the right by `c`
is injective on the left. -/
structure right [has_mul R] (c : R) : Prop :=
( mul_right_inj : ∀ a b : R, a * c = b * c → a = b)

variables [monoid R]

/-- An element admitting a right inverse is right-regular. -/
lemma right_of_mul_eq_one {a ai : R} (h : a * ai = 1) : right a :=
{ mul_right_inj :=
begin
  intros b c bc,
  rw [← mul_one b, ← mul_one c, ← h, ← mul_assoc, ← mul_assoc],
  exact congr_fun (congr_arg has_mul.mul bc) ai,
end }

/-- An element admitting a left inverse is left-regular. -/
lemma left_of_mul_eq_one {a ai : R} (h : ai * a = 1) : left a :=
{ mul_left_inj :=
begin
  intros b c bc,
  rw [← one_mul b, ← one_mul c, ← h, mul_assoc, mul_assoc],
  exact congr_arg (has_mul.mul ai) bc,
end }

lemma of_left_right {a : R} (hl : left a) (hr : right a) : is_regular a :=
⟨hl.1, hr.1⟩

lemma of_mul_eq_one_mul_eq_one {a ai : R} (hr : a * ai = 1) (hl : ai * a = 1) :
  is_regular a :=
of_left_right (left_of_mul_eq_one hl) (right_of_mul_eq_one hr)

end is_regular

open is_regular

/-- A unit is regular. -/
lemma is_unit.is_regular [monoid R] {a : R} (ua : is_unit a) : is_regular a :=
begin
  rcases ua with ⟨⟨t1, t2⟩, u, v⟩,
  exact of_mul_eq_one_mul_eq_one ua_w_val_inv ua_w_inv_val
end
