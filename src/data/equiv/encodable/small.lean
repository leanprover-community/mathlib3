/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.equiv.encodable.basic
import logic.small

/-!
# All encodable types are small.

That is, any encodable type is equivalent to a type in any universe.
-/

universes w v

@[priority 100]
instance small_of_encodable (α : Type v) [encodable α] : small.{w} α :=
small_of_injective _ (encodable.encode_injective)
