/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.multiset.basic
import data.list.range

/-! # `multiset.range n` gives `{0, 1, ..., n-1}` as a multiset. -/

open list nat

namespace multiset

/- range -/

/-- `range n` is the multiset lifted from the list `range n`,
  that is, the set `{0, 1, ..., n-1}`. -/
def range (n : ℕ) : multiset ℕ := range n

@[simp] theorem range_zero : range 0 = 0 := rfl

@[simp] theorem range_succ (n : ℕ) : range (succ n) = n ::ₘ range n :=
by rw [range, range_succ, ← coe_add, add_comm]; refl

@[simp] theorem card_range (n : ℕ) : card (range n) = n := length_range _

theorem range_subset {m n : ℕ} : range m ⊆ range n ↔ m ≤ n := range_subset

@[simp] theorem mem_range {m n : ℕ} : m ∈ range n ↔ m < n := mem_range

@[simp] theorem not_mem_range_self {n : ℕ} : n ∉ range n := not_mem_range_self

theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) := list.self_mem_range_succ n

end multiset
