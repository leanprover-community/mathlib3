/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.list.nodup

/-!
# Erasure of duplicates in a list

This file proves basic results about `list.dedup` (definition in `data.list.defs`).
`dedup l` returns `l` without its duplicates. It keeps the earliest (that is, rightmost)
occurrence of each.

## Tags

duplicate, multiplicity, nodup, `nub`
-/

universes u

namespace list

variables {α : Type u} [decidable_eq α]

@[simp] theorem dedup_nil : dedup [] = ([] : list α) := rfl

theorem dedup_cons_of_mem' {a : α} {l : list α} (h : a ∈ dedup l) :
  dedup (a :: l) = dedup l :=
pw_filter_cons_of_neg $ by simpa only [forall_mem_ne] using h

theorem dedup_cons_of_not_mem' {a : α} {l : list α} (h : a ∉ dedup l) :
  dedup (a :: l) = a :: dedup l :=
pw_filter_cons_of_pos $ by simpa only [forall_mem_ne] using h

@[simp] theorem mem_dedup {a : α} {l : list α} : a ∈ dedup l ↔ a ∈ l :=
by simpa only [dedup, forall_mem_ne, not_not] using not_congr (@forall_mem_pw_filter α (≠) _
  (λ x y z xz, not_and_distrib.1 $ mt (and.rec eq.trans) xz) a l)

@[simp] theorem dedup_cons_of_mem {a : α} {l : list α} (h : a ∈ l) :
  dedup (a :: l) = dedup l :=
dedup_cons_of_mem' $ mem_dedup.2 h

@[simp] theorem dedup_cons_of_not_mem {a : α} {l : list α} (h : a ∉ l) :
  dedup (a :: l) = a :: dedup l :=
dedup_cons_of_not_mem' $ mt mem_dedup.1 h

theorem dedup_sublist : ∀ (l : list α), dedup l <+ l := pw_filter_sublist

theorem dedup_subset : ∀ (l : list α), dedup l ⊆ l := pw_filter_subset

theorem subset_dedup (l : list α) : l ⊆ dedup l :=
λ a, mem_dedup.2

theorem nodup_dedup : ∀ l : list α, nodup (dedup l) := pairwise_pw_filter

theorem dedup_eq_self {l : list α} : dedup l = l ↔ nodup l := pw_filter_eq_self

protected lemma nodup.dedup {l : list α} (h : l.nodup) : l.dedup = l :=
list.dedup_eq_self.2 h

@[simp] theorem dedup_idempotent {l : list α} : dedup (dedup l) = dedup l :=
pw_filter_idempotent

theorem dedup_append (l₁ l₂ : list α) : dedup (l₁ ++ l₂) = l₁ ∪ dedup l₂ :=
begin
  induction l₁ with a l₁ IH, {refl}, rw [cons_union, ← IH],
  show dedup (a :: (l₁ ++ l₂)) = insert a (dedup (l₁ ++ l₂)),
  by_cases a ∈ dedup (l₁ ++ l₂);
  [ rw [dedup_cons_of_mem' h, insert_of_mem h],
    rw [dedup_cons_of_not_mem' h, insert_of_not_mem h]]
end

end list
