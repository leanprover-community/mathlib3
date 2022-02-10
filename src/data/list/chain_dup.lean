/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez, Eric Wieser
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

@[simp] lemma chain_dedup_nil : chain_dedup a [] = [] := rfl

lemma chain_dedup_cons :
  (b :: l).chain_dedup a = if a = b then chain_dedup b l else b :: chain_dedup b l := rfl

@[simp] lemma chain_dedup_cons' : (a :: l).chain_dedup a = l.chain_dedup a :=
by rw [chain_dedup, if_pos rfl]

@[simp] lemma chain_dedup_cons_of_ne (h : a ≠ b) : (a :: l).chain_dedup b = a :: l.chain_dedup a :=
by rw [chain_dedup, if_neg h.symm]

@[simp] lemma chain_dedup_singleton : [b].chain_dedup a = if a = b then [] else [b] :=
by split_ifs; simp! [h]

lemma chain_dedup_sublist : l.chain_dedup a <+ l :=
begin
  induction l with h l hl generalizing a,
  { simp },
  obtain rfl | hab := eq_or_ne a h,
  { rw chain_dedup_cons',
    exact (hl a).cons _ _ _ },
  { rw chain_dedup_cons_of_ne _ _ _ hab.symm,
    exact (hl _).cons2 _ _ _ }
end

lemma chain_dedup_is_chain : (l.chain_dedup a).chain ne a :=
begin
  induction l with h l hl generalizing a,
  { simp },
  rw chain_dedup,
  split_ifs with hih,
  { exact hih ▸ hl a },
  { exact chain_cons.mpr ⟨hih, hl h⟩ }
end

lemma chain_dedup_of_chain (h : l.chain ne a) : l.chain_dedup a = l :=
begin
  induction l with b l hb generalizing a,
  { exact list.chain_dedup_nil _ },
  obtain ⟨h, hc⟩ := chain_cons.mp h,
  rw [chain_dedup_cons_of_ne _ _ _ h.symm, hb _ hc],
end

@[simp] lemma chain_dedup_eq_self_iff : l.chain_dedup a = l ↔ l.chain ne a :=
⟨λ h, h ▸ chain_dedup_is_chain _ _, chain_dedup_of_chain _ _⟩

@[simp] lemma chain'_dedup_nil : ([] : list α).chain'_dedup = [] := rfl

lemma chain'_dedup_cons' : (a :: l).chain'_dedup = a :: chain_dedup a l := rfl

lemma chain'_dedup_cons_cons : (a :: b :: l).chain'_dedup =
  a :: if a = b then chain_dedup b l else b :: chain_dedup b l := rfl

@[simp] lemma chain'_dedup_singleton : chain'_dedup [a] = [a] := rfl

@[simp] lemma chain'_dedup_pair : chain'_dedup [a, b] = if a = b then [a] else [a, b] :=
(chain'_dedup_cons_cons _ _ _).trans $ apply_ite _ _ _ _

@[simp] lemma chain'_dedup_cons_cons' : (a :: a :: l).chain'_dedup = (a :: l).chain'_dedup :=
show _, from congr_arg (cons a) $ l.chain_dedup_cons' a

lemma chain'_dedup_sublist : ∀ (l : list α), l.chain'_dedup <+ l
| [] := sublist.slnil
| (h :: t) := (chain_dedup_sublist _ _).cons2 _ _ _

lemma chain'_dedup_is_chain' : ∀ (l : list α), l.chain'_dedup.chain' ne
| [] := list.chain'_nil
| (h :: l) := l.chain_dedup_is_chain h

lemma chain'_dedup_of_chain' : ∀ (l : list α), l.chain' ne → l.chain'_dedup = l
| [] h := rfl
| (a :: l) h := congr_arg (list.cons a) (chain_dedup_of_chain _ _ h)

@[simp] lemma chain'_dedup_eq_self_iff : l.chain'_dedup = l ↔ l.chain' ne :=
⟨λ h, h ▸ chain'_dedup_is_chain' _, chain'_dedup_of_chain' _⟩

lemma chain'_dedup_idem : l.chain'_dedup.chain'_dedup = l.chain'_dedup :=
chain'_dedup_of_chain' _ $ l.chain'_dedup_is_chain'

@[simp] lemma chain'_dedup_eq_nil : ∀ {l : list α}, chain'_dedup l = [] ↔ l = []
| [] := iff.rfl
| (a :: l) := ⟨λ h, list.no_confusion h, λ h, h.symm ▸ chain'_dedup_nil⟩

end list
