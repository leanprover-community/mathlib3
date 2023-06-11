/-
Copyright (c) 2023 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.locally_finite
import order.upper_lower.basic

/-!
# Upper and lower sets in a locally finite order

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we characterise the interaction of `upper_set`/`lower_set` and `locally_finite_order`.
-/

namespace set
variables {α : Type*} [preorder α] {s : set α}

protected lemma finite.upper_closure [locally_finite_order_top α] (hs : s.finite) :
  (upper_closure s : set α).finite :=
by { rw coe_upper_closure, exact hs.bUnion (λ _ _, finite_Ici _) }

protected lemma finite.lower_closure [locally_finite_order_bot α] (hs : s.finite) :
  (lower_closure s : set α).finite :=
by { rw coe_lower_closure, exact hs.bUnion (λ _ _, finite_Iic _) }

end set
