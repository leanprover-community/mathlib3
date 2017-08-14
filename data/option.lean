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

def map {α β : Type u} (f : α → β) : option α → option β
| (some x) := some (f x)
| none     := none

end option
