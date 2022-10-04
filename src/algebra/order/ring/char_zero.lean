/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import algebra.char_zero.defs
import algebra.order.ring.basic

/-!
# Linearly ordered semirings have characteristic zero.
-/

variables {α : Type*}

/-- Note this is not an instance as `char_zero` implies `nontrivial`,
and this would risk forming a loop. -/
lemma ordered_semiring.to_char_zero [nontrivial α] [ordered_semiring α] : char_zero α :=
⟨nat.strict_mono_cast.injective⟩

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_semiring.to_char_zero [linear_ordered_semiring α] : char_zero α :=
ordered_semiring.to_char_zero
