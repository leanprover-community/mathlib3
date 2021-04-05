/-
Copyright (c) 2021 Omri Ben-Eliezer. All rights reserved.
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

variables {α : Type*}


namespace heap
open tree

/-- Value held by the root of a tree. -/
@[simp]
def root : tree α → with_top α
| nil := ⊤
| (node x t₁ t₂) := x

/-- Number of nodes in heap. -/
@[simp]
def size : tree α → ℕ
| nil := 0
| (node x t₁ t₂) := size t₁ + size t₂ + 1

/-- Lemma: tree with size 0 is nil. -/
@[simp]
lemma tree_sized_zero_is_nil {T : tree α} : size T = 0 ↔ T = nil :=
begin
cases T,
simp only [size, eq_self_iff_true],
simp,
end

/-- Minimum distance of node to nil, walking down branches.
-/
def dist_to_nil : tree α → ℕ
| nil            := 0
| (node x t₁ t₂) := min (dist_to_nil t₁) (dist_to_nil t₂) + 1

variables [linear_order α]

/-- Check whether a given tree satisfies the heap invariant. -/
def is_heap : tree α → Prop
| nil            := true
| (node x t₁ t₂) := ((x : with_top α) ≤ root t₁) ∧
                    ((x : with_top α) ≤ root t₂) ∧
                    is_heap t₁ ∧ is_heap t₂

lemma is_heap.left {x : α} {t₁ t₂ : tree α} (h : is_heap (node x t₁ t₂)) : is_heap t₁ :=
h.2.2.1

lemma is_heap.right {x : α} {t₁ t₂ : tree α} (h : is_heap (node x t₁ t₂)) : is_heap t₂ :=
h.2.2.2

/-- Lemma: tree with one element is a heap. -/
lemma is_heap_single (x : α) : is_heap (node x nil nil) :=
⟨ le_top, le_top, trivial, trivial ⟩

/-- Insertion of a new node with given value to heap
-/
@[simp]
def insert : α → tree α → tree α
| y nil            := node y nil nil
| y (node x t₁ t₂) :=
  if dist_to_nil t₁ ≤ dist_to_nil t₂
  then node (min x y) (insert (max x y) t₁) t₂
  else node (min x y) t₁ (insert (max x y) t₂)

/-- Lemma: root of heap after insertion equals min(heap root, new element). -/
@[simp]
lemma root_insert (x : α) (t : tree α) : root (insert x t) = min x (root t) :=
begin
  cases t with y₁ t₁ t₂,
  { simp },
  { simp only [insert, root],
    split_ifs,
    { simp [min_comm] },
    { simp [min_comm] } }
end

/-- Lemma: Insertion of element to heap results in a valid heap. -/
lemma is_heap_insert (x : α) {t : tree α} (h : is_heap t) : is_heap (insert x t) :=
begin
  induction t with y t₁ t₂ iht₁ iht₂ generalizing x,
  { exact is_heap_single x },
  { simp [insert], rcases h with ⟨h₁, h₂, ht₁, ht₂⟩, split_ifs,
    { refine ⟨_, _, _, _⟩,
      { simp [le_refl, h₁], },
      { simp [le_refl, h₂], },
      { apply iht₁ ht₁,  },
      { exact ht₂, } },
    { refine ⟨_, _, _, _⟩,
      { simp [le_refl, h₁] },
      { simp [le_refl, h₂] },
      { exact ht₁, },
      { apply iht₂ ht₂, } } }
end

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

@[simp] lemma sift_down_nil_left (t : tree α) : sift_down nil t = t :=
by cases t; simp [sift_down]

@[simp] lemma sift_down_nil_right (t : tree α) : sift_down t nil = t :=
by cases t; simp [sift_down]

/-- Lemma: heap root of `sift_down` holds minimum value between the child subtrees. -/
@[simp]
lemma sift_down_root {H₁ H₂ : tree α} :
  root (sift_down H₁ H₂) = min (root H₁) (root H₂) :=
begin
  cases H₁; cases H₂;
  simp [sift_down],
  split_ifs,
  simp only [*, min_eq_left, root, with_top.coe_le_coe],
  simp only [root],
  simp [le_of_not_ge h],
end

/- Lemma: Sifting down two heaps gives a heap. -/
lemma is_heap_sift_down {t s : tree α} (ht : is_heap t) (hs : is_heap s) :
  is_heap (sift_down t s) :=
begin
  generalize hn : max (size t) (size s) = n, have := hn.le, clear hn,
  induction n with n ih generalizing s t,
  { simp at this, rcases this with ⟨rfl, rfl⟩, trivial },
  { cases t with x t₁ t₂; cases s with y s₁ s₂,
    { simp },
    { simp [-is_heap, *] },
    { simp [-is_heap, *] },
    rcases ⟨hs, ht⟩ with ⟨⟨_, _, _, _⟩, _, _, _, _⟩,
    simp only [nat.succ_eq_add_one, max_le_iff, size, add_le_add_iff_right] at this,
    cases this,
    simp only [sift_down], split_ifs,
    { suffices : is_heap (sift_down t₁ t₂), { simp [is_heap, *] },
      suffices : size t₁ ≤ n ∧ size t₂ ≤ n, { apply ih; simp * },
      split; linarith },
    { suffices : is_heap (sift_down s₁ s₂), { simp [is_heap, le_of_not_ge h, *] },
      suffices : size s₁ ≤ n ∧ size s₂ ≤ n, { apply ih; simp * },
      split; linarith } },
end

/-- Removing root from heap and rebalncing to preserve heap invariant. See also `sift_down`.
-/
def pop : tree α → tree α
| nil := nil
| (node x t1 t2) := sift_down t1 t2

/- Lemma: Popping an element preserves heap invariant. -/
lemma is_heap_pop {t : tree α} (ht : is_heap t) : is_heap (pop t) :=
begin
  cases t with y t₁ t₂,
  { trivial },
  { rcases ht with ⟨h₁, h₂, h₃, h₄⟩, apply is_heap_sift_down h₃ h₄ },
end

end heap
