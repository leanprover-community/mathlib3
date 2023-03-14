/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.list.nodup

/-!
# Erasure of duplicates in a list

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
  (λ x y z xz, not_and_distrib.1 $ mt (λ h, eq.trans h.1 h.2) xz) a l)

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

lemma replicate_dedup {x : α} : ∀ {k}, k ≠ 0 → (replicate k x).dedup = [x]
| 0 h := (h rfl).elim
| 1 _ := rfl
| (n+2) _ := by rw [replicate_succ, dedup_cons_of_mem (mem_replicate.2 ⟨n.succ_ne_zero, rfl⟩),
    replicate_dedup n.succ_ne_zero]

lemma count_dedup (l : list α) (a : α) :
  l.dedup.count a = if a ∈ l then 1 else 0 :=
by simp_rw [count_eq_of_nodup $ nodup_dedup l, mem_dedup]

/-- Summing the count of `x` over a list filtered by some `p` is just `countp` applied to `p` -/
lemma sum_map_count_dedup_filter_eq_countp (p : α → Prop) [decidable_pred p]
  (l : list α) : ((l.dedup.filter p).map $ λ x, l.count x).sum = l.countp p :=
begin
  induction l with a as h,
  { simp },
  { simp_rw [list.countp_cons, list.count_cons', list.sum_map_add],
    congr' 1,
    { refine trans _ h,
      by_cases ha : a ∈ as,
      { simp [dedup_cons_of_mem ha] },
      { simp only [dedup_cons_of_not_mem ha, list.filter],
        split_ifs with hp; simp [list.map_cons, list.sum_cons,
          list.count_eq_zero.2 ha, zero_add] } },
    { by_cases hp : p a,
      { refine trans (sum_map_eq_nsmul_single a _ (λ _ h _, by simp [h])) _,
        simp [hp, count_dedup] },
      { refine trans (list.sum_eq_zero $ λ n hn, _) (by simp [hp]),
        obtain ⟨a', ha'⟩ := list.mem_map.1 hn,
        simp only [(λ h, hp (h ▸ (list.mem_filter.1 ha'.1).2) : a' ≠ a), if_false] at ha',
        exact ha'.2.symm } } },
end

lemma sum_map_count_dedup_eq_length (l : list α) :
  (l.dedup.map $ λ x, l.count x).sum = l.length :=
by simpa using sum_map_count_dedup_filter_eq_countp (λ _, true) l

end list
