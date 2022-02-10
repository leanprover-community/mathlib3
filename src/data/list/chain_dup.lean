/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import data.list.chain

/-!
# Chain Deduplication of Lists

This file defines `list.chain'_dedup`, which removes all duplicates that are adjacent in a list,
e.g. `[2, 2, 3, 3, 2].chain'_dedup = [2, 3, 2]`.

## Main definitions

* `list.chain'_dedup`: removes all adjacent duplicates in a list.

## Main statements

* `list.chain'_dedup_sublist`: `l.chain'_dedup` is a sublist of `l`.
* `list.chain'_dedup_is_chain'`: `l.chain'_dedup` satisfies `chain' ne`.

## Tags

adjacent, chain, duplicates, remove, list
-/


variables {α : Type*} [decidable_eq α] (a b : α) (l : list α)

namespace list

/-- Removes all adjacent duplicates in `a :: l`. -/
def chain_dedup : α → list α → list α
| a [] := []
| a (h :: l) := if a = h then chain_dedup h l else h :: chain_dedup h l

@[simp] lemma chain_dedup_nil : chain_dedup a [] = [] := rfl

lemma chain_dedup_cons :
  (b :: l).chain_dedup a = if a = b then chain_dedup b l else b :: chain_dedup b l := rfl

@[simp] lemma chain_dedup_cons' : (a :: l).chain_dedup a = l.chain_dedup a :=
by rw [chain_dedup, if_pos rfl]

@[simp] lemma chain_dedup_singleton : [b].chain_dedup a = if a = b then [] else [b] :=
by split_ifs; simp! [h]

lemma chain_dedup_is_chain : (l.chain_dedup a).chain ne a :=
begin
  induction l with h l hl generalizing a,
  { simp },
  rw chain_dedup,
  split_ifs with hih,
  { exact hih ▸ hl a },
  { exact chain_cons.mpr ⟨hih, hl h⟩ }
end

/-- Removes all adjacent duplicates in a list. -/
def chain'_dedup : list α → list α
| (h :: l) := h :: chain_dedup h l
| [] := []

@[simp] lemma chain'_dedup_nil : ([] : list α).chain'_dedup = [] := rfl

lemma chain'_dedup_cons' : (a :: l).chain'_dedup = a :: chain_dedup a l := rfl

lemma chain'_dedup_cons_cons : (a :: b :: l).chain'_dedup =
  a :: if a = b then chain_dedup b l else b :: chain_dedup b l := rfl

@[simp] lemma chain'_dedup_singleton : chain'_dedup [a] = [a] := rfl

@[simp] lemma chain'_dedup_pair :
  chain'_dedup [a, b] = if a = b then [a] else [a, b] :=
by split_ifs; simp [chain'_dedup, h]

@[simp] lemma chain'_dedup_cons_cons' : (a :: a :: l).chain'_dedup = (a :: l).chain'_dedup :=
show _, from congr_arg (cons a) $ l.chain_dedup_cons' a

lemma chain'_dedup_eq_or_eq : (a :: l).chain'_dedup = l.chain'_dedup ∨
  (a :: l).chain'_dedup = a :: l.chain'_dedup :=
begin
  induction l with h l hl,
  { simp },
  rw [chain'_dedup_cons_cons],
  split_ifs with h; simp [h, chain'_dedup]
end

lemma chain'_dedup_sublist : l.chain'_dedup <+ l :=
begin
  induction l with h l hl,
  { simp },
  cases chain'_dedup_eq_or_eq h l with h h; rw h,
  { exact hl.cons _ _ _ },
  { exact hl.cons2 _ _ _ }
end

lemma chain'_dedup_is_chain' : l.chain'_dedup.chain' ne :=
begin
  induction l with h l hl,
  { simp },
  exact l.chain_dedup_is_chain h
end

lemma chain'_dedup_of_chain (h : l.chain' ne) : l.chain'_dedup = l :=
begin
  induction l with a l ha,
  { simp },
  cases l with b l,
  { simp },
  have := chain'_cons.mp h,
  specialize ha this.2,
  rw [chain'_dedup_cons_cons, if_neg this.1, ←chain'_dedup, ha]
end

lemma chain_dedup_idem : l.chain'_dedup.chain'_dedup = l.chain'_dedup :=
chain'_dedup_of_chain _ $ l.chain'_dedup_is_chain'

end list
