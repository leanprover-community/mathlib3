/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.multiset.nodup

/-!
# Erasing duplicates in a multiset.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

namespace multiset
open list

variables {α β : Type*} [decidable_eq α]

/-! ### dedup -/

/-- `dedup s` removes duplicates from `s`, yielding a `nodup` multiset. -/
def dedup (s : multiset α) : multiset α :=
quot.lift_on s (λ l, (l.dedup : multiset α))
  (λ s t p, quot.sound p.dedup)

@[simp] theorem coe_dedup (l : list α) : @dedup α _ l = l.dedup := rfl

@[simp] theorem dedup_zero : @dedup α _ 0 = 0 := rfl

@[simp] theorem mem_dedup {a : α} {s : multiset α} : a ∈ dedup s ↔ a ∈ s :=
quot.induction_on s $ λ l, mem_dedup

@[simp] theorem dedup_cons_of_mem {a : α} {s : multiset α} : a ∈ s →
  dedup (a ::ₘ s) = dedup s :=
quot.induction_on s $ λ l m, @congr_arg _ _ _ _ coe $ dedup_cons_of_mem m

@[simp] theorem dedup_cons_of_not_mem {a : α} {s : multiset α} : a ∉ s →
  dedup (a ::ₘ s) = a ::ₘ dedup s :=
quot.induction_on s $ λ l m, congr_arg coe $ dedup_cons_of_not_mem m

theorem dedup_le (s : multiset α) : dedup s ≤ s :=
quot.induction_on s $ λ l, (dedup_sublist _).subperm

theorem dedup_subset (s : multiset α) : dedup s ⊆ s :=
subset_of_le $ dedup_le _

theorem subset_dedup (s : multiset α) : s ⊆ dedup s :=
λ a, mem_dedup.2

@[simp] theorem dedup_subset' {s t : multiset α} : dedup s ⊆ t ↔ s ⊆ t :=
⟨subset.trans (subset_dedup _), subset.trans (dedup_subset _)⟩

@[simp] theorem subset_dedup' {s t : multiset α} : s ⊆ dedup t ↔ s ⊆ t :=
⟨λ h, subset.trans h (dedup_subset _), λ h, subset.trans h (subset_dedup _)⟩

@[simp] theorem nodup_dedup (s : multiset α) : nodup (dedup s) :=
quot.induction_on s nodup_dedup

theorem dedup_eq_self {s : multiset α} : dedup s = s ↔ nodup s :=
⟨λ e, e ▸ nodup_dedup s,
 quot.induction_on s $ λ l h, congr_arg coe h.dedup⟩

alias dedup_eq_self ↔ _ nodup.dedup

lemma count_dedup (m : multiset α) (a : α) :
  m.dedup.count a = if a ∈ m then 1 else 0 :=
quot.induction_on m $ λ l, count_dedup _ _

@[simp] lemma dedup_idempotent {m : multiset α} :
  m.dedup.dedup = m.dedup :=
quot.induction_on m $ λ l, @congr_arg _ _ _ _ coe dedup_idempotent

@[simp] lemma dedup_bind_dedup [decidable_eq β] (m : multiset α) (f : α → multiset β) :
  (m.dedup.bind f).dedup = (m.bind f).dedup :=
by { ext x, simp_rw [count_dedup, mem_bind, mem_dedup], }

theorem dedup_eq_zero {s : multiset α} : dedup s = 0 ↔ s = 0 :=
⟨λ h, eq_zero_of_subset_zero $ h ▸ subset_dedup _,
 λ h, h.symm ▸ dedup_zero⟩

@[simp] theorem dedup_singleton {a : α} : dedup ({a} : multiset α) = {a} :=
(nodup_singleton _).dedup

theorem le_dedup {s t : multiset α} : s ≤ dedup t ↔ s ≤ t ∧ nodup s :=
⟨λ h, ⟨le_trans h (dedup_le _), nodup_of_le h (nodup_dedup _)⟩,
 λ ⟨l, d⟩, (le_iff_subset d).2 $ subset.trans (subset_of_le l) (subset_dedup _)⟩

theorem le_dedup_self {s : multiset α} : s ≤ dedup s ↔ nodup s :=
by rw [le_dedup, and_iff_right le_rfl]

theorem dedup_ext {s t : multiset α} : dedup s = dedup t ↔ ∀ a, a ∈ s ↔ a ∈ t :=
by simp [nodup.ext]

theorem dedup_map_dedup_eq [decidable_eq β] (f : α → β) (s : multiset α) :
  dedup (map f (dedup s)) = dedup (map f s) := by simp [dedup_ext]

@[simp]
lemma dedup_nsmul {s : multiset α} {n : ℕ} (h0 : n ≠ 0) :
  (n • s).dedup = s.dedup :=
begin
  ext a,
  by_cases h : a ∈ s;
  simp [h,h0]
end

lemma nodup.le_dedup_iff_le {s t : multiset α} (hno : s.nodup) :
  s ≤ t.dedup ↔ s ≤ t :=
by simp [le_dedup, hno]

end multiset

lemma multiset.nodup.le_nsmul_iff_le {α : Type*} {s t : multiset α}
  {n : ℕ} (h : s.nodup) (hn : n ≠ 0) :
  s ≤ n • t ↔ s ≤ t :=
begin
  classical,
  rw [← h.le_dedup_iff_le, iff.comm, ← h.le_dedup_iff_le],
  simp [hn]
end
