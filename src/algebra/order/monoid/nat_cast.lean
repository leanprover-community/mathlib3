/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Yuyang Zhao
-/
import algebra.order.monoid.lemmas
import algebra.order.zero_le_one
import data.nat.cast.defs

/-!
# Order of numerials in an `add_monoid_with_one`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variable {α : Type*}

open function

lemma lt_add_one [has_one α] [add_zero_class α] [partial_order α] [zero_le_one_class α]
  [ne_zero (1 : α)] [covariant_class α α (+) (<)] (a : α) : a < a + 1 :=
lt_add_of_pos_right _ zero_lt_one

lemma lt_one_add [has_one α] [add_zero_class α] [partial_order α] [zero_le_one_class α]
  [ne_zero (1 : α)] [covariant_class α α (swap (+)) (<)] (a : α) : a < 1 + a :=
lt_add_of_pos_left _ zero_lt_one

variable [add_monoid_with_one α]

lemma zero_le_two [preorder α] [zero_le_one_class α] [covariant_class α α (+) (≤)] :
  (0 : α) ≤ 2 :=
add_nonneg zero_le_one zero_le_one

lemma zero_le_three [preorder α] [zero_le_one_class α] [covariant_class α α (+) (≤)] :
  (0 : α) ≤ 3 :=
add_nonneg zero_le_two zero_le_one

lemma zero_le_four [preorder α] [zero_le_one_class α] [covariant_class α α (+) (≤)] :
  (0 : α) ≤ 4 :=
add_nonneg zero_le_two zero_le_two

lemma one_le_two [has_le α] [zero_le_one_class α] [covariant_class α α (+) (≤)] :
  (1 : α) ≤ 2 :=
calc 1 = 1 + 0 : (add_zero 1).symm
   ... ≤ 1 + 1 : add_le_add_left zero_le_one _

lemma one_le_two' [has_le α] [zero_le_one_class α] [covariant_class α α (swap (+)) (≤)] :
  (1 : α) ≤ 2 :=
calc 1 = 0 + 1 : (zero_add 1).symm
   ... ≤ 1 + 1 : add_le_add_right zero_le_one _

section
variables [partial_order α] [zero_le_one_class α] [ne_zero (1 : α)]

section
variables [covariant_class α α (+) (≤)]

/-- See `zero_lt_two'` for a version with the type explicit. -/
@[simp] lemma zero_lt_two : (0 : α) < 2 := zero_lt_one.trans_le one_le_two
/-- See `zero_lt_three'` for a version with the type explicit. -/
@[simp] lemma zero_lt_three : (0 : α) < 3 := lt_add_of_lt_of_nonneg zero_lt_two zero_le_one
/-- See `zero_lt_four'` for a version with the type explicit. -/
@[simp] lemma zero_lt_four : (0 : α) < 4 := lt_add_of_lt_of_nonneg zero_lt_two zero_le_two

variables (α)

/-- See `zero_lt_two` for a version with the type implicit. -/
lemma zero_lt_two' : (0 : α) < 2 := zero_lt_two
/-- See `zero_lt_three` for a version with the type implicit. -/
lemma zero_lt_three' : (0 : α) < 3 := zero_lt_three
/-- See `zero_lt_four` for a version with the type implicit. -/
lemma zero_lt_four' : (0 : α) < 4 := zero_lt_four

instance zero_le_one_class.ne_zero.two : ne_zero (2 : α) := ⟨zero_lt_two.ne'⟩
instance zero_le_one_class.ne_zero.three : ne_zero (3 : α) := ⟨zero_lt_three.ne'⟩
instance zero_le_one_class.ne_zero.four : ne_zero (4 : α) := ⟨zero_lt_four.ne'⟩

end

lemma one_lt_two [covariant_class α α (+) (<)] : (1 : α) < 2 := lt_add_one _

end

alias zero_lt_two ← two_pos
alias zero_lt_three ← three_pos
alias zero_lt_four ← four_pos
