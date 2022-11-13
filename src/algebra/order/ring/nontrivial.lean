/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import algebra.char_zero.defs
import algebra.order.ring.defs

/-!
# Nontrivial strict ordered semirings (and hence linear ordered semirings) are characteristic zero.
-/

variables {α : Type*}

section strict_ordered_semiring
variables [strict_ordered_semiring α] [nontrivial α]

/-- Note this is not an instance as `char_zero` implies `nontrivial`, and this would risk forming a
loop. -/
lemma strict_ordered_semiring.to_char_zero : char_zero α := ⟨nat.strict_mono_cast.injective⟩

end strict_ordered_semiring

section linear_ordered_semiring
variables [linear_ordered_semiring α]

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_semiring.to_char_zero : char_zero α :=
strict_ordered_semiring.to_char_zero

end linear_ordered_semiring
