/-
Copyright (c) 2022 Tomaz Gomes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes
-/
import data.list.sort
import data.nat.log
import tactic.linarith
/-!
# Timed Insertion Sort
  This file defines a new version of Insertion Sort that, besides sorting the input list, counts the
  number of comparisons made through the execution of the algorithm. Also, it presents proofs of
  it's time complexity and it's equivalence to the one defined in data/list/sort.lean
## Main Definition
  - Timed.insertion_sort : list α → (list α × ℕ)
## Main Results
  - Timed.insertion_sort_complexity :
      ∀ l : list α, (Timed.insertion_sort r l).snd ≤ l.length * l.length
  - Timed.insertion_sort_equivalence :
      ∀ l : list α, (Timed.insertion_sort r l).fst = list.insertion_sort r l
-/

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

namespace timed

/-- `ordered_insert a l` inserts `a` into `l` at such that
  `ordered_insert a l` is sorted if `l` is. It also returns
  the number of comparisons performed. -/
@[simp] def ordered_insert (a : α) : list α → (list α × ℕ)
| []       := ([a], 0)
| (h :: t) := if a ≼ h then (a :: h :: t, 1)
              else let (l', n) := ordered_insert t in (h :: l', n + 1)

/-- Implementation of the insertion sort algorithm, modified
  to also return the number of operations performed. -/
@[simp] def insertion_sort : list α → (list α × ℕ)
| [] := ([], 0)
| (h :: t) := let (l', n) := (insertion_sort t), (l'', m) := ordered_insert r h l'
              in (l'', n + m)

theorem ordered_insert_complexity (a : α) :
  ∀ l : list α, (ordered_insert r a l).snd ≤ l.length :=
begin
  intro l,
  induction l,
  { simp only [list.length, ordered_insert], },
  { simp only [list.length, ordered_insert], split_ifs,
    { simp only [zero_le, le_add_iff_nonneg_left], },
    { cases (ordered_insert r a l_tl),
      unfold ordered_insert,
      linarith, } }
end

theorem ordered_insert_equivalence (a : α) : ∀ l : list α,
  (ordered_insert r a l).fst = list.ordered_insert r a l :=
begin
  intro l,
  induction l,
  { simp only [list.ordered_insert_nil, ordered_insert, eq_self_iff_true, and_self], },
  { simp only [list.ordered_insert, ordered_insert], split_ifs,
    { simp only [eq_self_iff_true, and_self], },
    { cases (ordered_insert r a l_tl),
      unfold ordered_insert,
      simp only [true_and, eq_self_iff_true],
      exact l_ih, } }
end

theorem ordered_insert_length (a : α) : ∀ l : list α,
  (ordered_insert r a l).fst.length = l.length + 1 :=
begin
  intro l,
  rw ordered_insert_equivalence r a l,
  exact list.ordered_insert_length r l a,
end

theorem insertion_sort_preserves_length : ∀ l : list α,
  (insertion_sort r l).fst.length = l.length :=
begin
  intro l,
  induction l,
  { simp only [insertion_sort], },
  { simp only [insertion_sort, list.length],
    cases (insertion_sort r l_tl) with sorted_tl _,
    unfold insertion_sort,
    have ordered_length : (ordered_insert r l_hd sorted_tl).fst.length = sorted_tl.length + 1 :=
      ordered_insert_length r l_hd sorted_tl,
    cases (ordered_insert r l_hd sorted_tl) with sorted_list _,
    unfold insertion_sort,
    rw ordered_length,
    rw l_ih, }
end

theorem insertion_sort_complexity :
  ∀ l : list α, (insertion_sort r l).snd ≤ l.length * l.length :=
begin
  intro l,
  induction l,
  { simp only [insertion_sort, list.length, mul_zero], },
  { simp only [insertion_sort, list.length],
    have same_lengths : (insertion_sort r l_tl).fst.length = l_tl.length :=
      insertion_sort_preserves_length r l_tl,
    cases (insertion_sort r l_tl) with sorted_tl ops,
    unfold insertion_sort,
    have hh : (ordered_insert r l_hd sorted_tl).snd ≤ sorted_tl.length :=
      ordered_insert_complexity r l_hd sorted_tl,
    cases (ordered_insert r l_hd sorted_tl),
    unfold insertion_sort,
    linarith, }
end

theorem insertion_sort_equivalence : ∀ l : list α,
  (insertion_sort r l).fst = list.insertion_sort r l :=
begin
  intro l,
  induction l,
  { simp only [insertion_sort, list.insertion_sort], },
  { simp only [insertion_sort, list.insertion_sort],
    rw ← l_ih,
    cases insertion_sort r l_tl,
    unfold insertion_sort,
    rw ← ordered_insert_equivalence r l_hd fst,
    cases ordered_insert r l_hd fst,
    unfold insertion_sort, }
end

end timed
