/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import data.list.basic

/-!
# Pairwise Deduplication of Lists

This file defines `list.no_pairwise_dup`, which removes all duplicates that are adjacent in a list,
e.g. `[2, 2, 3, 3, 2].no_pairwise_dup = [2, 3, 2]`.

## Main definitions

* `list.no_pairwise_dup`: removes all adjacent duplicates in a list.

## Main statements

* `list.no_pairwise_dup_sublist`: `l.no_pairwise_dup` is a sublist of `l`.

## Implementation details

We use `list.no_pairwise_dup_aux` as a way to implement `list.no_pairwise_dup`.

## Tags

adjacent, pairwise, duplicates, remove, list
-/


variables {α : Type*} [decidable_eq α] (a b : α) (l : list α)

namespace list

/-- Implements `list.no_pairwise_dup`. -/
def no_pairwise_dup_aux : α → list α → list α
| a [] := []
| a (h :: l) := if a = h then no_pairwise_dup_aux h l else h :: no_pairwise_dup_aux h l

@[simp] lemma no_pairwise_dup_aux_nil : no_pairwise_dup_aux a [] = [] := rfl

/-- Removes all adjacent duplicates in a list. -/
def no_pairwise_dup : list α → list α
| (h :: l) := h :: no_pairwise_dup_aux h l
| [] := []

@[simp] lemma no_pairwise_dup_nil : ([] : list α).no_pairwise_dup = [] := rfl

lemma no_pairwise_dup_cons' : (a :: l).no_pairwise_dup = a :: no_pairwise_dup_aux a l := rfl

lemma no_pairwise_dup_cons_cons' : (a :: b :: l).no_pairwise_dup =
  a :: if a = b then no_pairwise_dup_aux b l else b :: no_pairwise_dup_aux b l := rfl

@[simp] lemma no_pairwise_dup_singleton : no_pairwise_dup [a] = [a] := rfl

@[simp] lemma no_pairwise_dup_pair :
  no_pairwise_dup [a, b] = if a = b then [a] else [a, b] :=
by split_ifs; simp [no_pairwise_dup_cons_cons', h]

@[simp]
lemma no_pairwise_dup_cons_cons : (a :: a :: l).no_pairwise_dup = (a :: l).no_pairwise_dup :=
by { rw [no_pairwise_dup_cons_cons', if_pos rfl], refl }

lemma no_pairwise_dup_eq_or_eq : (a :: l).no_pairwise_dup = l.no_pairwise_dup ∨
  (a :: l).no_pairwise_dup = a :: l.no_pairwise_dup :=
begin
  induction l with h l hl,
  { simp },
  rw [no_pairwise_dup_cons_cons'],
  split_ifs with h; simp [h, no_pairwise_dup]
end

lemma no_pairwise_dup_sublist : l.no_pairwise_dup <+ l :=
begin
  induction l with h l hl,
  { simp },
  cases no_pairwise_dup_eq_or_eq h l with h h; rw h,
  { exact hl.cons _ _ _ },
  { exact hl.cons2 _ _ _ }
end

end list
