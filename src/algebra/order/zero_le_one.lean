/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import order.basic
import algebra.ne_zero

/-!
# Typeclass expressing `0 ≤ 1`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}

open function

/-- Typeclass for expressing that the `0` of a type is less or equal to its `1`. -/
class zero_le_one_class (α : Type*) [has_zero α] [has_one α] [has_le α] :=
(zero_le_one : (0 : α) ≤ 1)

/-- `zero_le_one` with the type argument implicit. -/
@[simp] lemma zero_le_one [has_zero α] [has_one α] [has_le α] [zero_le_one_class α] : (0 : α) ≤ 1 :=
zero_le_one_class.zero_le_one

/-- `zero_le_one` with the type argument explicit. -/
lemma zero_le_one' (α) [has_zero α] [has_one α] [has_le α] [zero_le_one_class α] : (0 : α) ≤ 1 :=
zero_le_one

section
variables [has_zero α] [has_one α] [partial_order α] [zero_le_one_class α] [ne_zero (1 : α)]

/-- See `zero_lt_one'` for a version with the type explicit. -/
@[simp] lemma zero_lt_one : (0 : α) < 1 := zero_le_one.lt_of_ne (ne_zero.ne' 1)

variables (α)

/-- See `zero_lt_one` for a version with the type implicit. -/
lemma zero_lt_one' : (0 : α) < 1 := zero_lt_one

end

alias zero_lt_one ← one_pos
