/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.group.defs
import algebra.covariant_and_contravariant
import algebra.order.monoid.lemmas

/-!
# Typeclass expressing `0 ≤ 1`.
-/

variables {α : Type*}

open function

/-- Typeclass for expressing that the `0` of a type is less or equal to its `1`. -/
class zero_le_one_class (α : Type*) [has_zero α] [has_one α] [has_le α] :=
(zero_le_one : (0 : α) ≤ 1)

@[simp] lemma zero_le_one [has_zero α] [has_one α] [has_le α] [zero_le_one_class α] : (0 : α) ≤ 1 :=
zero_le_one_class.zero_le_one

/- `zero_le_one` with an explicit type argument. -/
lemma zero_le_one' (α) [has_zero α] [has_one α] [has_le α] [zero_le_one_class α] : (0 : α) ≤ 1 :=
zero_le_one

lemma zero_le_two [preorder α] [has_one α] [add_zero_class α] [zero_le_one_class α]
  [covariant_class α α (+) (≤)] : (0 : α) ≤ 2 :=
add_nonneg zero_le_one zero_le_one

lemma zero_le_three [preorder α] [has_one α] [add_zero_class α] [zero_le_one_class α]
  [covariant_class α α (+) (≤)] : (0 : α) ≤ 3 :=
add_nonneg zero_le_two zero_le_one

lemma zero_le_four [preorder α] [has_one α] [add_zero_class α] [zero_le_one_class α]
  [covariant_class α α (+) (≤)] : (0 : α) ≤ 4 :=
add_nonneg zero_le_two zero_le_two

lemma one_le_two [has_le α] [has_one α] [add_zero_class α] [zero_le_one_class α]
  [covariant_class α α (+) (≤)] : (1 : α) ≤ 2 :=
calc 1 = 1 + 0 : (add_zero 1).symm
   ... ≤ 1 + 1 : add_le_add_left zero_le_one _

lemma one_le_two' [has_le α] [has_one α] [add_zero_class α] [zero_le_one_class α]
  [covariant_class α α (swap (+)) (≤)] : (1 : α) ≤ 2 :=
calc 1 = 0 + 1 : (zero_add 1).symm
   ... ≤ 1 + 1 : add_le_add_right zero_le_one _
