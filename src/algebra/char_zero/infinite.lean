/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.char_zero.defs
import data.fintype.card

/-! # A characteristic-zero semiring is infinite 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/

open set
variables (M : Type*) [add_monoid_with_one M] [char_zero M]

@[priority 100] -- see Note [lower instance priority]
instance char_zero.infinite : infinite M :=
infinite.of_injective coe nat.cast_injective
