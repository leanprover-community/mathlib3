/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

-- TODO: minimize these imports
import algebra.group_with_zero
import ring_theory.witt_vector.basic
import analysis.special_functions.trigonometric

open lean.parser

namespace baby_calc

section standard_lemmas

variables {α : Type*}

/-! ## EQ -/

/-! ### mul -/

lemma left_mul_cancel [left_cancel_semigroup α] {a b : α} (c : α)
  (h : c * a = c * b) : a = b := (mul_right_inj c).mp h

lemma right_mul_cancel [right_cancel_semigroup α] {a b : α} (c : α)
  (h : a * c = b * c) : a = b := (mul_left_inj c).mp h

lemma left_mul_cancel' [cancel_monoid_with_zero α] {a b : α} (c : α)
  (hc : c ≠ 0) (h : c * a = c * b) : a = b := (mul_right_inj' hc).mp h

lemma right_mul_cancel' [cancel_monoid_with_zero α] {a b : α} (c : α)
  (hc : c ≠ 0) (h : a * c = b * c) : a = b := (mul_left_inj'  hc).mp h

/-! ### add -/

lemma left_add_cancel [add_left_cancel_semigroup α] {a b : α} (c : α)
  (h : c + a = c + b) : a = b := (add_right_inj c).mp h

lemma right_add_cancel [add_right_cancel_semigroup α] {a b : α} (c : α)
  (h : a + c = b + c) : a = b := (add_left_inj c).mp h

/-! ### sub -/

lemma left_sub_cancel [add_group α] {a b : α} (c : α)
  (h : c - a = c - b) : a = b := sub_right_inj.mp h

lemma right_sub_cancel [add_group α] {a b : α} (c : α)
  (h : a - c = b - c) : a = b := sub_left_inj.mp h

/-! ## LE/LT -/

/-! ## mul -/

lemma left_le_of_mul_le_mul [ordered_cancel_comm_monoid α] {a b : α} (c : α)
  (h : c * a ≤ c * b) : a ≤ b := (mul_le_mul_iff_left c).mp h

lemma right_le_of_mul_le_mul [ordered_cancel_comm_monoid α] {a b : α} (c : α)
  (h : a * c ≤ b * c) : a ≤ b := (mul_le_mul_iff_right c).mp h

lemma left_lt_of_mul_lt_mul [ordered_cancel_comm_monoid α] {a b : α} (c : α)
  (h : c * a < c * b) : a < b := (mul_lt_mul_iff_left c).mp h

lemma right_lt_of_mul_lt_mul [ordered_cancel_comm_monoid α] {a b : α} (c : α)
  (h : a * c < b * c) : a < b := (mul_lt_mul_iff_right c).mp h

section linear_ordered_semiring
variables [linear_ordered_semiring α] {a b : α} (c : α)

lemma left_le_of_mul_le_mul_pos (hc : 0 < c)
  (h : c * a ≤ c * b) : a ≤ b := (mul_le_mul_left hc).mp h

lemma right_le_of_mul_le_mul_pos (hc : 0 < c)
  (h : a * c ≤ b * c) : a ≤ b := (mul_le_mul_right hc).mp h

lemma left_lt_of_mul_lt_mul_pos (hc : 0 < c)
  (h : c * a < c * b) : a < b := (mul_lt_mul_left hc).mp h

lemma right_lt_of_mul_lt_mul_pos (hc : 0 < c)
  (h : a * c < b * c) : a < b := (mul_lt_mul_right hc).mp h

end linear_ordered_semiring

section linear_ordered_ring
variables [linear_ordered_ring α] {a b : α} (c : α)

lemma left_le_of_mul_le_mul_neg (hc : c < 0)
  (h : c * a ≤ c * b) : b ≤ a := (mul_le_mul_left_of_neg hc).mp h

lemma right_le_of_mul_le_mul_neg (hc : c < 0)
  (h : a * c ≤ b * c) : b ≤ a := (mul_le_mul_right_of_neg hc).mp h

lemma left_lt_of_mul_lt_mul_neg (hc : c < 0)
  (h : c * a < c * b) : b < a := (mul_lt_mul_left_of_neg hc).mp h

lemma right_lt_of_mul_lt_mul_neg (hc : c < 0)
  (h : a * c < b * c) : b < a := (mul_lt_mul_right_of_neg hc).mp h

end linear_ordered_ring

end standard_lemmas

@[derive [decidable_eq, has_reflect, inhabited]]
inductive side | L | R

@[derive [decidable_eq, has_reflect, inhabited]]
inductive op | mul | add | sub

@[derive [decidable_eq, has_reflect, inhabited]]
inductive sign | pos | neg

@[derive [decidable_eq, has_reflect, inhabited]]
inductive rel | eq | le | lt | ne -- can we pull this last one off?

open side op sign

def lookup_list : list ((side × op × option sign) × name) :=
[ /- EQ -/
  /- mul -/
  ((L, mul, none), `left_mul_cancel),
  ((R, mul, none), `right_mul_cancel),
  ((L, mul, none), `left_mul_cancel'),
  ((R, mul, none), `right_mul_cancel'),
  /- add -/
  ((L, add, none), `left_add_cancel),
  ((R, add, none), `right_add_cancel),
  /- sub -/
  ((L, sub, none), `left_sub_cancel),
  ((R, sub, none), `right_sub_cancel),
  /- LE/LT -/
  /- mul -/
  ((L, mul, none), `left_le_of_mul_le_mul),
  ((R, mul, none), `right_le_of_mul_le_mul),
  ((L, mul, none), `left_lt_of_mul_lt_mul),
  ((R, mul, none), `right_lt_of_mul_lt_mul),
  ((L, mul, pos ), `left_le_of_mul_le_mul_pos),
  ((R, mul, pos ), `right_le_of_mul_le_mul_pos),
  ((L, mul, pos ), `left_lt_of_mul_lt_mul_pos),
  ((R, mul, pos ), `right_lt_of_mul_lt_mul_pos),
  ((L, mul, neg ), `left_le_of_mul_le_mul_neg),
  ((R, mul, neg ), `right_le_of_mul_le_mul_neg),
  ((L, mul, neg ), `left_lt_of_mul_lt_mul_neg),
  ((R, mul, neg ), `right_lt_of_mul_lt_mul_neg)
  ]

-- head → oper → side → option sign → list name

/-

## TODO
## Without order

### neg
add_group          `neg_inj`

### inv
group                   `inv_inj`
group_with_zero         `inv_inj'`

## With order

linear_ordered_semiring `mul_le_mul_left`    `mul_le_mul_right`

linear_ordered_ring      `mul_le_mul_left_of_neg`    `mul_le_mul_right_of_neg`

-/

end baby_calc
