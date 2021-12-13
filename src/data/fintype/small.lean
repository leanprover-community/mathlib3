/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.fintype.basic
import logic.small

/-!
# All finite types are small.

That is, any `α` with `[fintype α]` is equivalent to a type in any universe.

-/

universes w v

@[priority 100]
instance small_of_fintype (α : Type v) [fintype α] : small.{w} α :=
begin
  rw small_congr (fintype.equiv_fin α),
  apply_instance,
end
