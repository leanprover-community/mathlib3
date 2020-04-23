/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen

A typeclass for the two-sided multiplicative inverse.
-/

import tactic

/-!
# Invertible elements

This file defines a typeclass `invertible a` for elements `a` with a
multiplicative inverse.

The intent of the typeclass is to provide a way to write e.g. `⅟ 2` in a ring
like `ℤ[1/2]` where some inverses exist but there is no general `⁻¹` operator;
or to specify that a field has characteristic `≠ 2`.
It is the `Type`-valued analogue to the `Prop`-valued `is_unit`.

This file also includes some instances of `invertible`, notably for all elements
of a group and for some specific numbers if the characteristic is zero.
To find instances, `invertible_of_nonzero` is a useful definition.

## Notation

 * `⅟ a` is `invertible.inv_of a`, the inverse of `a`

## Implementation notes

The `invertible` class lives in `Type`, not `Prop`, to make computation easier.
If multiplication is associative, `invertible` is a subsingleton anyway.

The `simp` normal form tries to normalize `⅟ a` to `a ⁻¹`. Otherwise, it pushes
`⅟` inside the expression as much as possible.

## Tags

invertible, inverse element, inv_of, a half, one half, a third, one third, ½, ⅓

-/

universes u

variables {α : Type u}

/-- `invertible a` gives a two-sided multiplicative inverse of `a`. -/
class invertible [has_mul α] [has_one α] (a : α) : Type u :=
(inv_of : α) (inv_of_mul_self : inv_of * a = 1) (mul_inv_of_self : a * inv_of = 1)

-- This notation has the same precedence as `has_inv.inv`.
notation `⅟`:1034 := invertible.inv_of

@[simp]
lemma inv_of_mul_self [has_mul α] [has_one α] (a : α) [invertible a] : ⅟ a * a = 1 :=
invertible.inv_of_mul_self

@[simp]
lemma mul_inv_of_self [has_mul α] [has_one α] (a : α) [invertible a] : a * ⅟ a = 1 :=
invertible.mul_inv_of_self

@[simp]
lemma mul_inv_of_mul_self_cancel [monoid α] (a b : α) [invertible b] : a * ⅟ b * b = a :=
by simp [mul_assoc]

@[simp]
lemma mul_mul_inv_of_self_cancel [monoid α] (a b : α) [invertible b] : a * b * ⅟ b = a :=
by simp [mul_assoc]

lemma left_inv_eq_right_inv [monoid α] {a b c : α} (hba : b * a = 1) (hac : a * c = 1) : b = c :=
by rw [←one_mul c, ←hba, mul_assoc, hac, mul_one b]

instance [monoid α] (a : α) : subsingleton (invertible a) :=
⟨ λ ⟨b, hba, hab⟩ ⟨c, hca, hac⟩, by { congr, exact left_inv_eq_right_inv hba hac } ⟩

lemma is_unit_of_invertible [monoid α] (a : α) [invertible a] : is_unit a :=
⟨⟨a, ⅟ a, mul_inv_of_self a, inv_of_mul_self a⟩, rfl⟩

@[priority(100)]
instance invertible_of_group [group α] (a : α) : invertible a :=
⟨a⁻¹, inv_mul_self a, mul_inv_self a⟩

@[simp] lemma inv_of_eq_group_inv [group α] (a : α) : ⅟ a = a⁻¹ :=
rfl

instance invertible_one [monoid α] : invertible (1 : α) :=
⟨ 1, mul_one _, one_mul _ ⟩

@[simp] lemma inv_of_one [monoid α] : ⅟ (1 : α) = 1 := rfl

instance invertible_neg [ring α] (a : α) [invertible a] : invertible (-a) :=
⟨ -⅟a, by simp, by simp ⟩

@[simp] lemma inv_of_neg [ring α] (a : α) [invertible a] : ⅟(-a) = -⅟a := rfl

instance invertible_inv_of [has_one α] [has_mul α] {a : α} [invertible a] : invertible (⅟ a) :=
⟨ a, mul_inv_of_self a, inv_of_mul_self a ⟩

@[simp] lemma inv_of_inv_of [has_one α] [has_mul α] {a : α} [invertible a] : ⅟(⅟a) = a :=
rfl

instance invertible_mul [monoid α] (a b : α) [invertible a] [invertible b] : invertible (a * b) :=
⟨ ⅟b * ⅟a, by simp [←mul_assoc], by simp [←mul_assoc] ⟩

@[simp]
lemma inv_of_mul [monoid α] (a b : α) [invertible a] [invertible b] : ⅟(a * b) = ⅟b * ⅟a := rfl

section group_with_zero

variable [group_with_zero α]

lemma nonzero_of_invertible (a : α) [invertible a] : a ≠ 0 :=
λ ha, zero_ne_one $ calc   0 = ⅟ a * a : by simp [ha]
                         ... = 1 : inv_of_mul_self a

/-- `a⁻¹` is an inverse of `a` if `a ≠ 0` -/
def invertible_of_nonzero {a : α} (h : a ≠ 0) : invertible a :=
⟨ a⁻¹, inv_mul_cancel' _ h, mul_inv_cancel' _ h ⟩

@[simp] lemma inv_of_eq_inv (a : α) [invertible a] : ⅟ a = a⁻¹ :=
left_inv_eq_right_inv (inv_of_mul_self a) (mul_inv_cancel' _ (nonzero_of_invertible a))

@[simp] lemma inv_mul_cancel_of_invertible (a : α) [invertible a] : a⁻¹ * a = 1 :=
inv_mul_cancel' _ (nonzero_of_invertible a)

@[simp] lemma mul_inv_cancel_of_invertible (a : α) [invertible a] : a * a⁻¹ = 1 :=
mul_inv_cancel' _ (nonzero_of_invertible a)

@[simp] lemma div_mul_cancel_of_invertible (a b : α) [invertible b] : a / b * b = a :=
div_mul_cancel' a (nonzero_of_invertible b)

@[simp] lemma mul_div_cancel_of_invertible (a b : α) [invertible b] : a * b / b = a :=
mul_div_cancel'' a (nonzero_of_invertible b)

@[simp] lemma div_self_of_invertible (a : α) [invertible a] : a / a = 1 :=
div_self' (nonzero_of_invertible a)

instance invertible_div (a b : α) [invertible a] [invertible b] : invertible (a / b) :=
⟨ b / a, by simp [←mul_div_assoc''], by simp [←mul_div_assoc''] ⟩

@[simp] lemma inv_of_div (a b : α) [invertible a] [invertible b] : ⅟ (a / b) = b / a :=
rfl

instance invertible_inv {a : α} [invertible a] : invertible (a⁻¹) :=
⟨ a, by simp, by simp ⟩

end group_with_zero

section division_ring

variable [division_ring α]

instance invertible_succ [char_zero α] (n : ℕ) : invertible (n.succ : α) :=
invertible_of_nonzero (nat.cast_ne_zero.mpr (nat.succ_ne_zero _))

/-!
A few `invertible n` instances for small numerals `n`. Feel free to add your own
number when you need its inverse.
-/

instance invertible_two [char_zero α] : invertible (2 : α) :=
invertible_of_nonzero (by exact_mod_cast (dec_trivial : 2 ≠ 0))

instance invertible_three [char_zero α] : invertible (3 : α) :=
invertible_of_nonzero (by exact_mod_cast (dec_trivial : 3 ≠ 0))

end division_ring
