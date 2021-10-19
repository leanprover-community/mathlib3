/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.multiset.nodup

/-!
# Erasing duplicates in a multiset.
-/

namespace multiset
open list

variables {α β : Type*} [decidable_eq α]

/-! ### erase_dup -/

/-- `erase_dup s` removes duplicates from `s`, yielding a `nodup` multiset. -/
def erase_dup (s : multiset α) : multiset α :=
quot.lift_on s (λ l, (l.erase_dup : multiset α))
  (λ s t p, quot.sound p.erase_dup)

@[simp] theorem coe_erase_dup (l : list α) : @erase_dup α _ l = l.erase_dup := rfl

@[simp] theorem erase_dup_zero : @erase_dup α _ 0 = 0 := rfl

@[simp] theorem mem_erase_dup {a : α} {s : multiset α} : a ∈ erase_dup s ↔ a ∈ s :=
quot.induction_on s $ λ l, mem_erase_dup

@[simp] theorem erase_dup_cons_of_mem {a : α} {s : multiset α} : a ∈ s →
  erase_dup (a ::ₘ s) = erase_dup s :=
quot.induction_on s $ λ l m, @congr_arg _ _ _ _ coe $ erase_dup_cons_of_mem m

@[simp] theorem erase_dup_cons_of_not_mem {a : α} {s : multiset α} : a ∉ s →
  erase_dup (a ::ₘ s) = a ::ₘ erase_dup s :=
quot.induction_on s $ λ l m, congr_arg coe $ erase_dup_cons_of_not_mem m

theorem erase_dup_le (s : multiset α) : erase_dup s ≤ s :=
quot.induction_on s $ λ l, (erase_dup_sublist _).subperm

theorem erase_dup_subset (s : multiset α) : erase_dup s ⊆ s :=
subset_of_le $ erase_dup_le _

theorem subset_erase_dup (s : multiset α) : s ⊆ erase_dup s :=
λ a, mem_erase_dup.2

@[simp] theorem erase_dup_subset' {s t : multiset α} : erase_dup s ⊆ t ↔ s ⊆ t :=
⟨subset.trans (subset_erase_dup _), subset.trans (erase_dup_subset _)⟩

@[simp] theorem subset_erase_dup' {s t : multiset α} : s ⊆ erase_dup t ↔ s ⊆ t :=
⟨λ h, subset.trans h (erase_dup_subset _), λ h, subset.trans h (subset_erase_dup _)⟩

@[simp] theorem nodup_erase_dup (s : multiset α) : nodup (erase_dup s) :=
quot.induction_on s nodup_erase_dup

theorem erase_dup_eq_self {s : multiset α} : erase_dup s = s ↔ nodup s :=
⟨λ e, e ▸ nodup_erase_dup s,
 quot.induction_on s $ λ l h, congr_arg coe h.erase_dup⟩

alias erase_dup_eq_self ↔ _ multiset.nodup.erase_dup

alias erase_dup_eq_self ↔ _ multiset.nodup.erase_dup

theorem erase_dup_eq_zero {s : multiset α} : erase_dup s = 0 ↔ s = 0 :=
⟨λ h, eq_zero_of_subset_zero $ h ▸ subset_erase_dup _,
 λ h, h.symm ▸ erase_dup_zero⟩

@[simp] theorem erase_dup_singleton {a : α} : erase_dup ({a} : multiset α) = {a} :=
(nodup_singleton _).erase_dup

theorem le_erase_dup {s t : multiset α} : s ≤ erase_dup t ↔ s ≤ t ∧ nodup s :=
⟨λ h, ⟨le_trans h (erase_dup_le _), nodup_of_le h (nodup_erase_dup _)⟩,
 λ ⟨l, d⟩, (le_iff_subset d).2 $ subset.trans (subset_of_le l) (subset_erase_dup _)⟩

theorem erase_dup_ext {s t : multiset α} : erase_dup s = erase_dup t ↔ ∀ a, a ∈ s ↔ a ∈ t :=
by simp [nodup_ext]

theorem erase_dup_map_erase_dup_eq [decidable_eq β] (f : α → β) (s : multiset α) :
  erase_dup (map f (erase_dup s)) = erase_dup (map f s) := by simp [erase_dup_ext]

@[simp]
lemma erase_dup_nsmul {s : multiset α} {n : ℕ} (h0 : n ≠ 0) :
  (n • s).erase_dup = s.erase_dup :=
begin
  ext a,
  by_cases h : a ∈ s;
  simp [h,h0]
end

lemma nodup.le_erase_dup_iff_le {s t : multiset α} (hno : s.nodup) :
  s ≤ t.erase_dup ↔ s ≤ t :=
by simp [le_erase_dup, hno]

end multiset

lemma multiset.nodup.le_nsmul_iff_le {α : Type*} {s t : multiset α}
  {n : ℕ} (h : s.nodup) (hn : n ≠ 0) :
  s ≤ n • t ↔ s ≤ t :=
begin
  classical,
  rw [← h.le_erase_dup_iff_le, iff.comm, ← h.le_erase_dup_iff_le],
  simp [hn]
end
