/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.multiset.nodup
import data.list.intervals

/-!
# Intervals in ℕ as multisets

For now this only covers `Ico n m`, the "closed-open" interval containing `[n, ..., m-1]`.
-/

namespace multiset
open list

/-! ### Ico -/

/-- `Ico n m` is the multiset lifted from the list `Ico n m`, e.g. the set `{n, n+1, ..., m-1}`. -/
def Ico (n m : ℕ) : multiset ℕ := Ico n m

namespace Ico

theorem map_add (n m k : ℕ) : (Ico n m).map ((+) k) = Ico (n + k) (m + k) :=
congr_arg coe $ list.Ico.map_add _ _ _

theorem map_sub (n m k : ℕ) (h : k ≤ n) : (Ico n m).map (λ x, x - k) = Ico (n - k) (m - k) :=
congr_arg coe $ list.Ico.map_sub _ _ _ h

theorem zero_bot (n : ℕ) : Ico 0 n = range n :=
congr_arg coe $ list.Ico.zero_bot _

@[simp] theorem card (n m : ℕ) : (Ico n m).card = m - n :=
list.Ico.length _ _

theorem nodup (n m : ℕ) : nodup (Ico n m) := Ico.nodup _ _

@[simp] theorem mem {n m l : ℕ} : l ∈ Ico n m ↔ n ≤ l ∧ l < m :=
list.Ico.mem

theorem eq_zero_of_le {n m : ℕ} (h : m ≤ n) : Ico n m = 0 :=
congr_arg coe $ list.Ico.eq_nil_of_le h

@[simp] theorem self_eq_zero {n : ℕ} : Ico n n = 0 :=
eq_zero_of_le $ le_refl n

@[simp] theorem eq_zero_iff {n m : ℕ} : Ico n m = 0 ↔ m ≤ n :=
iff.trans (coe_eq_zero _) list.Ico.eq_empty_iff

lemma add_consecutive {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) :
  Ico n m + Ico m l = Ico n l :=
congr_arg coe $ list.Ico.append_consecutive hnm hml

@[simp] lemma inter_consecutive (n m l : ℕ) : Ico n m ∩ Ico m l = 0 :=
congr_arg coe $ list.Ico.bag_inter_consecutive n m l

@[simp] theorem succ_singleton {n : ℕ} : Ico n (n+1) = {n} :=
congr_arg coe $ list.Ico.succ_singleton

theorem succ_top {n m : ℕ} (h : n ≤ m) : Ico n (m + 1) = m ::ₘ Ico n m :=
by rw [Ico, list.Ico.succ_top h, ← coe_add, add_comm]; refl

theorem eq_cons {n m : ℕ} (h : n < m) : Ico n m = n ::ₘ Ico (n + 1) m :=
congr_arg coe $ list.Ico.eq_cons h

@[simp] theorem pred_singleton {m : ℕ} (h : 0 < m) : Ico (m - 1) m = {m - 1} :=
congr_arg coe $ list.Ico.pred_singleton h

@[simp] theorem not_mem_top {n m : ℕ} : m ∉ Ico n m :=
list.Ico.not_mem_top

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

lemma filter_le_of_le_bot {n m l : ℕ} (hln : l ≤ n) : (Ico n m).filter (λ x, l ≤ x) = Ico n m :=
congr_arg coe $ list.Ico.filter_le_of_le_bot hln

lemma filter_le_of_top_le {n m l : ℕ} (hml : m ≤ l) : (Ico n m).filter (λ x, l ≤ x) = ∅ :=
congr_arg coe $ list.Ico.filter_le_of_top_le hml

lemma filter_le_of_le {n m l : ℕ} (hnl : n ≤ l) : (Ico n m).filter (λ x, l ≤ x) = Ico l m :=
congr_arg coe $ list.Ico.filter_le_of_le hnl

@[simp] lemma filter_le (n m l : ℕ) : (Ico n m).filter (λ x, l ≤ x) = Ico (max n l) m :=
congr_arg coe $ list.Ico.filter_le n m l

end Ico
end multiset
