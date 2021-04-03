/-
Copyright (c) 2021 Mathlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Omri Ben-Eliezer, Floris van Doorn
-/

import data.tree
import order.bounded_lattice
import algebra.order_functions
import tactic

/-!
# Heap

A (minimum) heap is a tree data structure where each node holds a value, 
which is equal to or smaller than the values of its children (we henceforth 
call this the heap invariant or the heap condition). In this file we 
support some basic operations on heaps such as insertion of an element 
and deletion of the minimum element (i.e., popping the root).
-/

variables {α : Type*} [linear_order α]
#check with_top α

namespace heap
open tree

/-- Value held by the root of the heap -/
@[simp]
def heap_root : tree α → with_top α
| nil := ⊤
| (node x t₁ t₂) := x

/-- Check whether a given tree satisfies the heap invariant -/
def is_heap : tree α → Prop
| nil            := true
| (node x t₁ t₂) := ((x : with_top α) ≤ heap_root t₁) ∧
                    ((x : with_top α) ≤ heap_root t₂) ∧ 
                    is_heap t₁ ∧ is_heap t₂

/-- Number of nodes in heap -/
@[simp]
def size : tree α → ℕ 
| nil := 0
| (node x t₁ t₂) := (size t₁ + size t₂) + 1

/-- Maximum number of nodes from root to leaf 
among all branches of the heap 
-/
def depth : tree α → ℕ 
| nil := 0
| (node x t₁ t₂) := (max (depth t₁) (depth t₂)) + 1

/-- Minimum distance of node to nil, walking down branches
-/
def dist_to_nil : tree α → ℕ
| nil            := 0
| (node x t₁ t₂) := min (dist_to_nil t₁) (dist_to_nil t₂) + 1

/-- Insertion of a new node with given value to heap
-/
@[simp]
def insert : α → tree α → tree α
| y nil            := node y nil nil
| y (node x t₁ t₂) :=
  if dist_to_nil t₁ ≤ dist_to_nil t₂
  then node (min x y) (insert (max x y) t₁) t₂
  else node (min x y) t₁ (insert (max x y) t₂)

open well_founded_tactics
/-- Rebalancing heap (preserving heap invariant) when root is removed -- helper for `pop` procedure.
Recursively does the following: place value of minimum (immediate) child in current node,
then continue to that child.
-/
def sift_down : tree α → tree α → tree α
| nil t                         := t
| t nil                         := t
| (node x t₁ t₂) (node y s₁ s₂) :=
  have ht :  max (sizeof t₁) (sizeof t₂) < max (sizeof (node x t₁ t₂)) (sizeof (node y s₁ s₂)) :=
    by { refine (max_lt _ _).trans_le (le_max_left _ _); default_dec_tac },
  have hs :  max (sizeof s₁) (sizeof s₂) < max (sizeof (node x t₁ t₂)) (sizeof (node y s₁ s₂)) :=
    by { refine (max_lt _ _).trans_le (le_max_right _ _); default_dec_tac },
  if x ≤ y
    then node x (sift_down t₁ t₂) (node y s₁ s₂)
    else node y (node x t₁ t₂) (sift_down s₁ s₂)
using_well_founded { rel_tac := λ _ _, 
  `[exact ⟨ _, measure_wf (λ ⟨ arg1, arg2⟩, max (sizeof arg1) (sizeof arg2))⟩] }

/-- Removing root from heap and rebalncing to preserve heap invariant. See also `sift_down`
-/
def pop: tree α → tree α
| nil := nil
| (node x t1 t2) := sift_down t1 t2

/-- Lemma: tree with one element is a heap-/
lemma tree_with_single_element_is_heap {x : α} : is_heap (node x nil nil) :=
⟨ le_top, le_top, trivial, trivial ⟩ 

@[simp, norm_cast] lemma with_top.coe_min (x y : α) : ((min x y : α) : with_top α) = min x y :=
by simp [min, ite_cast]

/-- Lemma: root of heap after insertion equals min(heap root, new element) -/
@[simp]
lemma heap_root_val_after_insertion (x : α) (t : tree α) : 
  heap_root (insert x t) = min x (heap_root t) :=
begin
cases t with y₁ t₁ t₂,
{
  simp,
},
{
  simp only [insert, heap_root],
  split_ifs,
  {simp [min_comm]},
  {simp [min_comm]},
}
end

/-- Lemma: Insertion of element to heap results in a valid heap -/
lemma heap_after_insertion_is_heap {H : tree α} : is_heap H → ∀ (x : α), is_heap (insert x H) :=
begin
intros h₁ x,
induction H with y t₁ t₂ ih₁ ih₂ generalizing x,
{
unfold heap.insert,
exact tree_with_single_element_is_heap
},
{
unfold is_heap at h₁,
rcases h₁ with ⟨h₂, h₃, ht₁, ht₂⟩,
unfold insert,
split_ifs,
unfold is_heap,
refine ⟨_, _, _, _⟩,
simp [le_refl, h₂],
simp [le_refl, h₃],
apply ih₁,
assumption,
assumption,
unfold is_heap,
refine ⟨_, _, _, _⟩,
simp [le_refl, h₂],
simp [le_refl, h₃],
assumption,
apply ih₂,
assumption,
}
end

lemma le_iff_eq_of_le {x y : α} (h : x ≤ y) : x = y ↔ y ≤ x := 
by simp [eq_iff_le_not_lt, h]

lemma max_eq_add_one (n m k : ℕ) : max n m = k ↔ n ≤ k ∧ m ≤ k ∧ (n = k ∨ m = k) :=
by { rw [le_antisymm_iff], simp [and_assoc, le_iff_eq_of_le] {contextual := tt} }

@[simp] lemma nat.max_eq_zero (n m : ℕ) : max n m = 0 ↔ n = 0 ∧ m = 0 :=
by simp [max_eq_add_one] {contextual := tt}

/-- Lemma: tree with size 0 is nil-/
@[simp]
lemma tree_sized_zero_is_nil {T : tree α} : size T = 0 ↔ T = nil :=
begin
cases T,
simp only [size, eq_self_iff_true],
simp,
end

/-- Lemma: heap root of `sift_down` holds minimum value between the child subtrees-/
@[simp]
lemma sift_down_heap_root {H₁ H₂ : tree α} : 
  heap_root (sift_down H₁ H₂) = min (heap_root H₁) (heap_root H₂) :=
begin
  cases H₁; cases H₂;
  simp [sift_down],
  split_ifs,
  simp only [*, min_eq_left, heap_root, with_top.coe_le_coe],
  simp only [heap_root],
  simp [le_of_not_ge h],
end

/- Lemma: Sifting down two heaps gives a heap-/
lemma sift_down_heaps_is_heap {H₁ H₂ : tree α} : 
  is_heap H₁ ∧ is_heap H₂ → is_heap (sift_down H₁ H₂) :=
begin
generalize hn : max (size H₁) (size H₂) = n, 
have := hn.le, clear hn,
induction n with n ih generalizing H₁ H₂,
{
  simp at this,
  cases this,
  simp only [and_imp],
  simp [*, is_heap, sift_down],
},
{
  cases H₁ with x t₁ t₂;
  cases H₂ with y s₁ s₂,
  simp [is_heap, sift_down],
  simp [sift_down],
  simp [sift_down],
  intros h₁ h₂,
  exact h₁,
  intro h₃,
  simp [sift_down],
  unfold is_heap at h₃,
  rcases h₃ with ⟨ ⟨h₄₁, h₄₂, h₄₃, h₄₄⟩ , h₅ , h₆ , h₇ , h₈⟩ ,
  split_ifs,
  simp [is_heap, *],
  apply ih,
  simp [nat.succ_eq_add_one] at this,  
  cases this with h₉₁ h₉₂,
  simp only [max_le_iff],
  split,
  linarith,
  linarith,
  exact ⟨h₄₃, h₄₄⟩,
  have h' : y ≤ x,
  exact le_of_not_ge h,
  simp [is_heap, *],
  apply ih,
  simp [nat.succ_eq_add_one] at this,  
  cases this with h₉₁ h₉₂,
  simp only [max_le_iff],
  split,
  linarith,
  linarith,
  exact ⟨h₇, h₈⟩,
}
end

/- Lemma: Popping an element preserves heap invariant -/
lemma heap_after_pop_is_heap {H : tree α} : is_heap H → is_heap (pop H) := 
begin
cases H with y t₁ t₂, 
intro h,
trivial,
intro h,
apply sift_down_heaps_is_heap,
rcases h with ⟨h₁ , h₂ , h₃ , h₄⟩,
exact ⟨h₃, h₄⟩, 
end

end heap

#lint
