/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import algebra.char_zero
import data.fintype.basic

/-!
# Characteristic zero implies infinite.

This is kept separate from the main file about characteristic zero,
so that we can avoid needing to import anything about finiteness there.
This is useful as `algebra/char_zero.lean` is imported in many places, including tactics.

-/

variables {M : Type*} [add_monoid M] [has_one M] [char_zero M]

@[priority 100] -- see Note [lower instance priority]
instance char_zero.infinite : infinite M :=
infinite.of_injective coe nat.cast_injective
