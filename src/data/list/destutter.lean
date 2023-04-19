/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez, Eric Wieser
-/
import data.list.chain

/-!
# Destuttering of Lists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves theorems about `list.destutter` (in `data.list.defs`), which greedily removes all
non-related items that are adjacent in a list, e.g. `[2, 2, 3, 3, 2].destutter (≠) = [2, 3, 2]`.
Note that we make no guarantees of being the longest sublist with this property; e.g.,
`[123, 1, 2, 5, 543, 1000].destutter (<) = [123, 543, 1000]`, but a longer ascending chain could be
`[1, 2, 5, 543, 1000]`.

## Main statements

* `list.destutter_sublist`: `l.destutter` is a sublist of `l`.
* `list.destutter_is_chain'`: `l.destutter` satisfies `chain' R`.
* Analogies of these theorems for `list.destutter'`, which is the `destutter` equivalent of `chain`.

## Tags

adjacent, chain, duplicates, remove, list, stutter, destutter
-/

variables {α : Type*} (l : list α) (R : α → α → Prop) [decidable_rel R] {a b : α}

namespace list

@[simp] lemma destutter'_nil : destutter' R a [] = [a] := rfl

lemma destutter'_cons :
  (b :: l).destutter' R a = if R a b then a :: destutter' R b l else destutter' R a l := rfl

variables {R}

@[simp] lemma destutter'_cons_pos (h : R b a) :
  (a :: l).destutter' R b = b :: l.destutter' R a :=
by rw [destutter', if_pos h]

@[simp] lemma destutter'_cons_neg (h : ¬ R b a) :
  (a :: l).destutter' R b = l.destutter' R b :=
by rw [destutter', if_neg h]

variables (R)

@[simp] lemma destutter'_singleton : [b].destutter' R a = if R a b then [a, b] else [a] :=
by split_ifs; simp! [h]

lemma destutter'_sublist (a) : l.destutter' R a <+ a :: l :=
begin
  induction l with b l hl generalizing a,
  { simp },
  rw destutter',
  split_ifs,
  { exact sublist.cons2 _ _ _ (hl b) },
  { exact (hl a).trans ((l.sublist_cons b).cons_cons a) }
end

lemma mem_destutter' (a) : a ∈ l.destutter' R a :=
begin
  induction l with b l hl,
  { simp },
  rw destutter',
  split_ifs,
  { simp },
  { assumption }
end

lemma destutter'_is_chain : ∀ l : list α, ∀ {a b}, R a b → (l.destutter' R b).chain R a
| [] a b h := chain_singleton.mpr h
| (c :: l) a b h :=
begin
  rw destutter',
  split_ifs with hbc,
  { rw chain_cons,
    exact ⟨h, destutter'_is_chain l hbc⟩ },
  { exact destutter'_is_chain l h },
end

lemma destutter'_is_chain' (a) : (l.destutter' R a).chain' R :=
begin
  induction l with b l hl generalizing a,
  { simp },
  rw destutter',
  split_ifs,
  { exact destutter'_is_chain R l h },
  { exact hl a },
end

lemma destutter'_of_chain (h : l.chain R a) : l.destutter' R a = a :: l :=
begin
  induction l with b l hb generalizing a,
  { simp },
  obtain ⟨h, hc⟩ := chain_cons.mp h,
  rw [l.destutter'_cons_pos h, hb hc]
end

@[simp] lemma destutter'_eq_self_iff (a) : l.destutter' R a = a :: l ↔ l.chain R a :=
⟨λ h, by { rw [←chain', ←h], exact l.destutter'_is_chain' R a }, destutter'_of_chain _ _⟩

lemma destutter'_ne_nil : l.destutter' R a ≠ [] :=
ne_nil_of_mem $ l.mem_destutter' R a

@[simp] lemma destutter_nil : ([] : list α).destutter R = [] := rfl

lemma destutter_cons' : (a :: l).destutter R = destutter' R a l := rfl

lemma destutter_cons_cons : (a :: b :: l).destutter R =
  if R a b then a :: destutter' R b l else destutter' R a l := rfl

@[simp] lemma destutter_singleton : destutter R [a] = [a] := rfl

@[simp] lemma destutter_pair : destutter R [a, b] = if R a b then [a, b] else [a] :=
destutter_cons_cons _ R

lemma destutter_sublist : ∀ (l : list α), l.destutter R <+ l
| [] := sublist.slnil
| (h :: l) := l.destutter'_sublist R h

lemma destutter_is_chain' : ∀ (l : list α), (l.destutter R).chain' R
| [] := list.chain'_nil
| (h :: l) := l.destutter'_is_chain' R h

lemma destutter_of_chain' : ∀ (l : list α), l.chain' R → l.destutter R = l
| [] h := rfl
| (a :: l) h := l.destutter'_of_chain _ h

@[simp] lemma destutter_eq_self_iff : ∀ (l : list α), l.destutter R = l ↔ l.chain' R
| [] := by simp
| (a :: l) := l.destutter'_eq_self_iff R a

lemma destutter_idem : (l.destutter R).destutter R = l.destutter R :=
destutter_of_chain' R _ $ l.destutter_is_chain' R

@[simp] lemma destutter_eq_nil : ∀ {l : list α}, destutter R l = [] ↔ l = []
| [] := iff.rfl
| (a :: l) := ⟨λ h, absurd h $ l.destutter'_ne_nil R, λ h, match h with end⟩

end list
