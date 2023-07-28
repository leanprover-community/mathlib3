/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.fintype.card
import logic.small.basic

/-!
# All finite types are small.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

That is, any `α` with `[fintype α]` is equivalent to a type in any universe.

-/

universes w v

@[priority 100]
instance small_of_fintype (α : Type v) [fintype α] : small.{w} α :=
begin
  rw small_congr (fintype.equiv_fin α),
  apply_instance,
end
