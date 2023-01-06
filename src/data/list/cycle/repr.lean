/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.list.cycle.basic
import data.multiset.repr

/-!
# Representing a cycle as a string
-/

/--
We define a representation of concrete cycles, available when viewing them in a goal state or
via `#eval`, when over representatble types. For example, the cycle `(2 1 4 3)` will be shown
as `c[1, 4, 3, 2]`. The representation of the cycle sorts the elements by the string value of the
underlying element. This representation also supports cycles that can contain duplicates.
-/
instance {α : Type*} [has_repr α] : has_repr (cycle α) :=
⟨λ s, "c[" ++ string.intercalate ", " ((s.map repr).lists.sort (≤)).head ++ "]"⟩
