/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import logic.small.basic
import data.countable.defs

/-!
# All countable types are small.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

That is, any countable type is equivalent to a type in any universe.
-/

universes w v

@[priority 100]
instance small_of_countable (α : Type v) [countable α] : small.{w} α :=
let ⟨f, hf⟩ := exists_injective_nat α in small_of_injective hf
