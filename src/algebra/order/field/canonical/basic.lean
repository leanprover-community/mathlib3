/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import algebra.order.field.canonical.defs

/-!
# Lemmas about canonically ordered semifields.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/
variables {α : Type*}

section canonically_linear_ordered_semifield
variables [canonically_linear_ordered_semifield α] [has_sub α] [has_ordered_sub α]

lemma tsub_div (a b c : α) : (a - b) / c = a / c - b / c := by simp_rw [div_eq_mul_inv, tsub_mul]

end canonically_linear_ordered_semifield
