/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.list.sort
import data.multiset.basic
import data.string.basic

/-!
# Construct a sorted list from a multiset.
-/

namespace multiset
open list
variables {α : Type*}

section sort
variables (r : α → α → Prop) [decidable_rel r]
  [is_trans α r] [is_antisymm α r] [is_total α r]

/-- `sort s` constructs a sorted list from the multiset `s`.
  (Uses merge sort algorithm.) -/
def sort (s : multiset α) : list α :=
quot.lift_on s (merge_sort r) $ λ a b h,
eq_of_perm_of_sorted
  ((perm_merge_sort _ _).trans $ h.trans (perm_merge_sort _ _).symm)
  (sorted_merge_sort r _)
  (sorted_merge_sort r _)

@[simp] theorem coe_sort (l : list α) : sort r l = merge_sort r l := rfl

@[simp] theorem sort_sorted (s : multiset α) : sorted r (sort r s) :=
quot.induction_on s $ λ l, sorted_merge_sort r _

@[simp] theorem sort_eq (s : multiset α) : ↑(sort r s) = s :=
quot.induction_on s $ λ l, quot.sound $ perm_merge_sort _ _

@[simp] theorem mem_sort {s : multiset α} {a : α} : a ∈ sort r s ↔ a ∈ s :=
by rw [← mem_coe, sort_eq]

@[simp] theorem length_sort {s : multiset α} : (sort r s).length = s.card :=
quot.induction_on s $ length_merge_sort _

end sort

instance [has_repr α] : has_repr (multiset α) :=
⟨λ s, "{" ++ string.intercalate ", " ((s.map repr).sort (≤)) ++ "}"⟩

end multiset
