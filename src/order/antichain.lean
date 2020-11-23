/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import order.basic
import data.finset

/-!
# Antichains
Investigating the structure of finsets in a partial order.
We define antichains.

## Main definitions
* `antichain` is a family of sets where no set is a subset of another.
-/

open partial_order

universe u
variable {α : Type u}

section
variables [partial_order α]

/--
A set of elements of a partial order forms an antichain if no two elements
`A` and `B` are ordered `A < B`.
-/
def antichain (𝒜 : finset α) : Prop := ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≤ B → A = B

end
