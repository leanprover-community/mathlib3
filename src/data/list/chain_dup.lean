/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez, Eric Wieser
-/
import data.list.chain

/-!
# Chain Deduplication of Lists

This file proves theorems about `list.chain'_dedup` (in `data.list.defs`), which removes all
duplicates that are adjacent in a list, e.g. `[2, 2, 3, 3, 2].chain'_dedup (≠) = [2, 3, 2]`.

## Main statements

* `list.chain'_dedup_sublist`: `l.chain'_dedup` is a sublist of `l`.
* `list.chain'_dedup_is_chain'`: `l.chain'_dedup` satisfies `chain' ne`.

## Tags

adjacent, chain, duplicates, remove, list
-/

variables {α : Type*} (l : list α) (R : α → α → Prop) [decidable_rel R] {a b : α}

namespace list

@[simp] lemma chain_dedup_nil : chain_dedup R a [] = [a] := rfl

lemma chain_dedup_cons :
  (b :: l).chain_dedup R a = if R a b then a :: chain_dedup R b l else chain_dedup R a l := rfl

variables {R}

@[simp] lemma chain_dedup_cons_pos (h : R b a) :
  (a :: l).chain_dedup R b = b :: l.chain_dedup R a :=
by rw [chain_dedup, if_pos h]

@[simp] lemma chain_dedup_cons_neg (h : ¬ R b a) :
  (a :: l).chain_dedup R b = l.chain_dedup R b :=
by rw [chain_dedup, if_neg h]

variables (R)

@[simp] lemma chain_dedup_singleton : [b].chain_dedup R a = if R a b then [a, b] else [a] :=
by split_ifs; simp! [h]

lemma chain_dedup_sublist (a) : l.chain_dedup R a <+ a :: l :=
begin
  induction l with b l hl generalizing a,
  { simp },
  rw chain_dedup,
  split_ifs,
  { exact sublist.cons2 _ _ _ (hl b) },
  { exact (hl a).trans ((l.sublist_cons b).cons_cons a) }
end

lemma mem_chain_dedup (a) : a ∈ l.chain_dedup R a :=
begin
  induction l with b l hl,
  { simp },
  rw chain_dedup,
  split_ifs,
  { simp },
  { assumption }
end

lemma chain_dedup_is_chain : ∀ l : list α, ∀ {a b}, R a b → (l.chain_dedup R b).chain R a
| [] a b h := chain_singleton.mpr h
| (c :: l) a b h :=
begin
  rw chain_dedup,
  split_ifs with hbc,
  { rw chain_cons,
    exact ⟨h, chain_dedup_is_chain l hbc⟩ },
  { exact chain_dedup_is_chain l h },
end

lemma chain_dedup_is_chain' (a) : (l.chain_dedup R a).chain' R :=
begin
  induction l with b l hl generalizing a,
  { simp },
  rw chain_dedup,
  split_ifs,
  { exact chain_dedup_is_chain R l h },
  { exact hl a },
end

lemma chain_dedup_of_chain (h : l.chain R a) : l.chain_dedup R a = a :: l :=
begin
  induction l with b l hb generalizing a,
  { simp },
  obtain ⟨h, hc⟩ := chain_cons.mp h,
  rw [l.chain_dedup_cons_pos h, hb hc]
end

@[simp] lemma chain_dedup_eq_self_iff (a) : l.chain_dedup R a = a :: l ↔ l.chain R a :=
⟨λ h, by { rw [←chain', ←h], exact l.chain_dedup_is_chain' R a }, chain_dedup_of_chain _ _⟩

lemma chain_dedup_ne_nil : l.chain_dedup R a ≠ [] :=
ne_nil_of_mem $ l.mem_chain_dedup R a

@[simp] lemma chain'_dedup_nil : ([] : list α).chain'_dedup R = [] := rfl

lemma chain'_dedup_cons' : (a :: l).chain'_dedup R = chain_dedup R a l := rfl

lemma chain'_dedup_cons_cons : (a :: b :: l).chain'_dedup R =
  if R a b then a :: chain_dedup R b l else chain_dedup R a l := rfl

@[simp] lemma chain'_dedup_singleton : chain'_dedup R [a] = [a] := rfl

@[simp] lemma chain'_dedup_pair : chain'_dedup R [a, b] = if R a b then [a, b] else [a] :=
chain'_dedup_cons_cons _ R

lemma chain'_dedup_sublist : ∀ (l : list α), l.chain'_dedup R <+ l
| [] := sublist.slnil
| (h :: l) := l.chain_dedup_sublist R h

lemma chain'_dedup_is_chain' : ∀ (l : list α), (l.chain'_dedup R).chain' R
| [] := list.chain'_nil
| (h :: l) := l.chain_dedup_is_chain' R h

lemma chain'_dedup_of_chain' : ∀ (l : list α), l.chain' R → l.chain'_dedup R = l
| [] h := rfl
| (a :: l) h := l.chain_dedup_of_chain _ h

@[simp] lemma chain'_dedup_eq_self_iff : ∀ (l : list α), l.chain'_dedup R = l ↔ l.chain' R
| [] := by simp
| (a :: l) := l.chain_dedup_eq_self_iff R a

lemma chain'_dedup_idem : (l.chain'_dedup R).chain'_dedup R = l.chain'_dedup R :=
chain'_dedup_of_chain' R _ $ l.chain'_dedup_is_chain' R

@[simp] lemma chain'_dedup_eq_nil : ∀ {l : list α}, chain'_dedup R l = [] ↔ l = []
| [] := iff.rfl
| (a :: l) := ⟨λ h, absurd h $ l.chain_dedup_ne_nil R, λ h, match h with end⟩

end list
