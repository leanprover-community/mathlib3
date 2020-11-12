/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison, Anne Baanen
-/
import data.multiset.nodup
import data.list.enum

/-!
# Intervals in ℕ as multisets

For now this only covers `Ico n m`, the "closed-open" interval containing `[n, ..., m-1]`.
-/

namespace multiset
open list

/-! ### Ico -/

/-- `Ico n m` is the multiset lifted from the list `Ico n m`, i.e. the set `{n, n+1, ..., m-1}`. -/
def Ico {α : Type*} [has_enum α] (b t : α) : multiset α := list.Ico b t

namespace Ico

variables {α : Type*} [linear_order α] [has_lawful_enum α]

theorem map_add_ℕ (n m k : ℕ) : (Ico n m).map ((+) k) = Ico (k + n) (k + m) :=
congr_arg coe $ map_add_Ico_ℕ k n m

theorem map_sub_ℕ (n m k : ℕ) (h : k ≤ n) : (Ico n m).map (λ x, x - k) = Ico (n - k) (m - k) :=
congr_arg coe $ map_sub_Ico_ℕ k n m h

@[simp] theorem card_ℕ (n m : ℕ) : (Ico n m).card = m - n :=
length_Ico _ _

theorem nodup (n m : α) : nodup (Ico n m) :=
nodup_Ico _ _

@[simp] theorem mem {n m l : α} : l ∈ Ico n m ↔ n ≤ l ∧ l < m :=
mem_Ico

@[simp] theorem eq_zero {n m : α} : Ico n m = 0 ↔ m ≤ n :=
(coe_eq_zero _).trans list.Ico_eq_nil

@[simp] theorem self_eq_zero {n : α} : Ico n n = 0 :=
congr_arg coe $ Ico_self

lemma Ico_append_Ico {n m l : α} (hnm : n ≤ m) (hml : m ≤ l) :
  Ico n m + Ico m l = Ico n l :=
congr_arg coe $ Ico_append_Ico hnm hml

@[simp] lemma inter_consecutive (n m l : α) : Ico n m ∩ Ico m l = 0 :=
congr_arg coe $ list.Ico_bag_inter_Ico_consecutive n m l

@[simp] theorem succ_self (n : ℕ) : Ico n (n+1) = {n} :=
congr_arg coe $ list.Ico_succ_self n

theorem succ_right {n m : ℕ} (h : n ≤ m) : Ico n (m + 1) = m ::ₘ Ico n m :=
by { rw [Ico, list.Ico_succ_right' h, ← coe_add, add_comm], refl }

theorem eq_cons {n m : ℕ} (h : n < m) : Ico n m = n ::ₘ Ico (n + 1) m :=
congr_arg coe $ list.Ico_eq_cons h

@[simp] theorem pred_singleton {m : ℕ} (h : 0 < m) : Ico (m - 1) m = {m - 1} :=
congr_arg coe $ list.Ico_pred_self h

@[simp] theorem top_not_mem {n m : α} : m ∉ Ico n m :=
list.top_not_mem_Ico n m

lemma filter_lt_of_top_le {n m l : ℕ} (hml : m ≤ l) : (Ico n m).filter (λ x, x < l) = Ico n m :=
congr_arg coe $ list.Ico.filter_lt_of_top_le hml

lemma filter_lt_of_le_bot {n m l : ℕ} (hln : l ≤ n) : (Ico n m).filter (λ x, x < l) = ∅ :=
congr_arg coe $ list.Ico.filter_lt_of_le_bot hln

lemma filter_le_of_bot {n m : ℕ} (hnm : n < m) : (Ico n m).filter (λ x, x ≤ n) = {n} :=
congr_arg coe $ list.Ico.filter_le_of_bot hnm

lemma filter_lt_of_ge {n m l : ℕ} (hlm : l ≤ m) : (Ico n m).filter (λ x, x < l) = Ico n l :=
congr_arg coe $ list.Ico.filter_lt_of_ge hlm

@[simp] lemma filter_lt (n m l : ℕ) : (Ico n m).filter (λ x, x < l) = Ico n (min m l) :=
congr_arg coe $ list.Ico.filter_lt n m l

lemma le_filter_of_le_bot {n m l : ℕ} (hln : l ≤ n) : (Ico n m).filter (λ x, l ≤ x) = Ico n m :=
congr_arg coe $ list.Ico.le_filter_of_le_bot hln

lemma le_filter_le_of_top_le {n m l : ℕ} (hml : m ≤ l) : (Ico n m).filter (λ x, l ≤ x) = ∅ :=
congr_arg coe $ list.Ico.le_filter_of_top_le hml

lemma le_filter_of_le {n m l : ℕ} (hnl : n ≤ l) : (Ico n m).filter (λ x, l ≤ x) = Ico l m :=
congr_arg coe $ list.Ico.le_filter_of_le hnl

@[simp] lemma le_filter (n m l : ℕ) : (Ico n m).filter (λ x, l ≤ x) = Ico (max n l) m :=
congr_arg coe $ list.Ico.le_filter n m l

theorem subset_Ico {b t b' t' : α} (h : b < t) :
  Ico b t ⊆ Ico b' t' ↔ b' ≤ b ∧ t ≤ t' :=
coe_subset.trans (list.Ico_subset_Ico h)

theorem le_Ico {b t b' t' : α} (h : b < t) :
  Ico b t ≤ Ico b' t' ↔ b' ≤ b ∧ t ≤ t' :=
(le_iff_subset (nodup b t)).trans (subset_Ico h)

end Ico

section Ico_zero

open nat

@[simp] theorem Ico_zero_succ (n : ℕ) : Ico 0 (succ n) = n ::ₘ Ico 0 n :=
Ico.succ_right (nat.zero_le _)

@[simp] theorem card_Ico_zero (n : ℕ) : card (Ico 0 n) = n :=
Ico.card_ℕ _ _

@[simp] lemma Ico_zero_subset_Ico_zero {m n : ℕ} : Ico 0 m ⊆ Ico 0 n ↔ m ≤ n :=
if h : m = 0 then by simp [h]
else (Ico.subset_Ico (nat.pos_of_ne_zero h)).trans (by simp)

@[simp] theorem mem_Ico_zero {m n : ℕ} : m ∈ Ico 0 n ↔ m < n :=
by simp [mem_Ico]

@[simp] theorem not_mem_Ico_zero_self {n : ℕ} : n ∉ Ico 0 n :=
top_not_mem_Ico _ _

theorem self_mem_Ico_zero_succ (n : ℕ) : n ∈ Ico 0 (n + 1) :=
mem_Ico_zero.mpr (lt_add_one n)

theorem Ico_zero_le_Ico_zero {m n : ℕ} : Ico 0 m ≤ Ico 0 n ↔ m ≤ n :=
(le_iff_subset (Ico.nodup _ _)).trans Ico_zero_subset_Ico_zero

end Ico_zero

end multiset
