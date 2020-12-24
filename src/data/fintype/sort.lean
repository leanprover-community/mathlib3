/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.fintype.basic
import data.finset.sort

variables {α : Type*}

open finset

/-- Given a linearly ordered fintype `α` of cardinal `k`, the order isomorphism
`mono_equiv_of_fin α h` is the increasing bijection between `fin k` and `α`. Here, `h` is a proof
that the cardinality of `s` is `k`. We use this instead of an isomorphism `fin s.card ≃o α` to avoid
casting issues in further uses of this function. -/
def mono_equiv_of_fin (α) [fintype α] [linear_order α] {k : ℕ}
  (h : fintype.card α = k) : fin k ≃o α :=
(univ.order_iso_of_fin h).trans $ (order_iso.set_congr _ _ coe_univ).trans order_iso.set.univ
