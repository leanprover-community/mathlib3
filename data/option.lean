/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

universes u v

namespace option

@[reducible] def iget {α : Type u} [inhabited α] : option α → α
| (some x) := x
| none     := arbitrary α

def filter {α : Type u} (p : α → Prop) [decidable_pred p] : option α → option α
| none     := none
| (some a) := if p a then some a else none

end option
