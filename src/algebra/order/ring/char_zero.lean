/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import algebra.char_zero.defs
import algebra.order.ring.defs

/-!
# Strict ordered semiring have characteristic zero

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}

@[priority 100] -- see Note [lower instance priority]
instance strict_ordered_semiring.to_char_zero [strict_ordered_semiring α] : char_zero α :=
⟨strict_mono.injective $ strict_mono_nat_of_lt_succ $ λ n,
  by { rw [nat.cast_succ], apply lt_add_one }⟩
