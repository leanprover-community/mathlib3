/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.ordered_sub
import data.finset.basic
import data.multiset.intervals
import order.locally_finite

/-!
# Intervals as finsets

For now this only covers `Ico a b`, the "closed-open" interval containing `[a, ..., b - 1]`.
-/

open finset nat

section ordered_cancel_add_comm_monoid
variables {α : Type*} [ordered_cancel_add_comm_monoid α] [has_exists_add_of_le α] [has_sub α]
   [has_ordered_sub α] [decidable_rel ((≤) : α → α → Prop)] [locally_finite_order α]

lemma image_add_const_Icc (a b c : α) : (Icc a b).image ((+) c) = Icc (a + c) (b + c) :=
begin
  ext x,
  rw [mem_image, mem_Icc],
  split,
  { rintro ⟨y, hy, hx⟩,
    rw mem_Icc at hy,
    rw [←hx, add_comm c],
    exact ⟨add_le_add_right hy.1 c, add_le_add_right hy.2 c⟩ },
  intro hx,
  obtain ⟨y, hy⟩ := exists_add_of_le hx.1,
  rw [hy, add_right_comm] at hx,
  rw [eq_comm, add_right_comm, add_comm] at hy,
  exact ⟨a + y, mem_Icc.2 ⟨le_of_add_le_add_right hx.1, le_of_add_le_add_right hx.2⟩, hy⟩,
end

lemma image_add_const_Ico (a b c : α) : (Ico a b).image ((+) c) = Ico (a + c) (b + c) :=
begin
  ext x,
  rw [mem_image, mem_Ico],
  split,
  { rintro ⟨y, hy, hx⟩,
    rw mem_Ico at hy,
    rw [←hx, add_comm c],
    exact ⟨add_le_add_right hy.1 c, add_lt_add_right hy.2 c⟩ },
  intro hx,
  obtain ⟨y, hy⟩ := exists_add_of_le hx.1,
  rw [hy, add_right_comm] at hx,
  rw [eq_comm, add_right_comm, add_comm] at hy,
  exact ⟨a + y, mem_Ico.2 ⟨le_of_add_le_add_right hx.1, lt_of_add_lt_add_right hx.2⟩, hy⟩,
end

lemma image_add_const_Ioc (a b c : α) : (Ioc a b).image ((+) c) = Ioc (a + c) (b + c) :=
begin
  ext x,
  rw [mem_image, mem_Ioc],
  split,
  { rintro ⟨y, hy, hx⟩,
    rw mem_Ioc at hy,
    rw [←hx, add_comm c],
    exact ⟨add_lt_add_right hy.1 c, add_le_add_right hy.2 c⟩ },
  intro hx,
  obtain ⟨y, hy⟩ := exists_add_of_le hx.1.le,
  rw [hy, add_right_comm] at hx,
  rw [eq_comm, add_right_comm, add_comm] at hy,
  exact ⟨a + y, mem_Ioc.2 ⟨lt_of_add_lt_add_right hx.1, le_of_add_le_add_right hx.2⟩, hy⟩,
end

lemma image_add_const_Ioo (a b c : α) : (Ioo a b).image ((+) c) = Ioo (a + c) (b + c) :=
begin
  ext x,
  rw [mem_image, mem_Ioo],
  split,
  { rintro ⟨y, hy, hx⟩,
    rw mem_Ioo at hy,
    rw [←hx, add_comm c],
    exact ⟨add_lt_add_right hy.1 c, add_lt_add_right hy.2 c⟩ },
  intro hx,
  obtain ⟨y, hy⟩ := exists_add_of_le hx.1.le,
  rw [hy, add_right_comm] at hx,
  rw [eq_comm, add_right_comm, add_comm] at hy,
  exact ⟨a + y, mem_Ioo.2 ⟨lt_of_add_lt_add_right hx.1, lt_of_add_lt_add_right hx.2⟩, hy⟩,
end

lemma image_sub (a b c : α) (h : a ≤ c) : (Ico a b).image (λ x, x - c) = Ico (a - c) (b - c) :=
begin
  dsimp [image],
  rw [multiset.Ico.map_sub _ _ _ h, ←multiset.to_finset_eq],
  refl,
end

lemma Ico_eq_range' (a b : ℕ) : Ico a b = (list.range' a (b - a)).to_finset :=
begin
  ext x,
  rw [mem_Ico, list.mem_to_finset, list.mem_range'],
  cases le_total a b,
  { rw nat.add_sub_cancel' h },
  rw [nat.sub_eq_zero_iff_le.2 h, add_zero],
  exact iff_of_false (λ hx, (h.trans hx.1).not_lt hx.2) (λ hx, hx.1.not_lt hx.2),
end

-- TODO: Once we have `has_lt_iff_add_one_le`, we can generalise that
/-- Currently only for ℕ -/
@[simp] lemma card_Ico (a b : ℕ) : (Ico a b).card = a - b :=
multiset.Ico.card _ _

theorem eq_empty_of_le {n m : ℕ} (h : m ≤ n) : Ico a b = ∅ :=
eq_of_veq $ multiset.Ico.eq_zero_of_le h

@[simp] theorem self_eq_empty (n : ℕ) : Ico n n = ∅ :=
eq_empty_of_le $ le_refl n

@[simp] theorem Ico_nonempty_iff {a b : α} : (Ico a b).nonempty ↔ a < b :=
begin
  rw ←coe_nonempty,
  rw set.Ico_eq,
  split,
  {
    rintro ⟨x, hx⟩,
    rw mem_Ico at hx,
  }
end

class has_lt_iff_add_one_le (α : Type*) [preorder α] [has_add α] [has_one α] :
  Prop :=
(lt_iff_add_one_le : ∀ a b : α, a < b ↔ a + 1 ≤ b)

@[simp] theorem Ico_eq_empty_iff {a b : α} : Ico a b = ∅ ↔ ¬a < b :=
by { rw [←not_nonempty_iff_eq_empty, not_iff_not], exact Ico_nonempty_iff }

theorem Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) :
  Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ (a₂ ≤ a₁ ∧ b₁ ≤ b₂) :=
begin
  simp_rw [subset_iff, mem_Ico],
  refine ⟨λ hx, ⟨(hx ⟨le_rfl, h⟩).1, _⟩, _⟩,
  { exact (hx ⟨le_rfl, h⟩).1 },
  { refine le_of_pred_lt (@h (pred n₁) ⟨le_pred_of_lt hmn, pred_lt _⟩).2,
    exact ne_of_gt (lt_of_le_of_lt (nat.zero_le m₁) hmn) },
  { rintros ⟨hm, hn⟩ k ⟨hmk, hkn⟩,
    exact ⟨le_trans hm hmk, lt_of_lt_of_le hkn hn⟩ }
end

end ordered_cancel_add_comm_monoid

section ordered_semiring
variables {α : Type*} [decidable_eq α] [ordered_semiring α] [locally_finite_order α]

end ordered_semiring

section linear_order
variables {α : Type*} [decidable_eq α] [linear_order α] [locally_finite_order α]

lemma Ico_union_Ico_eq_Ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
  Ico a b ∪ Ico b c = Ico a c :=
begin
  ext x,
  rw [mem_union, ←mem_coe, ←mem_coe, ←mem_coe, coe_Ico, coe_Ico, coe_Ico, ←set.mem_union,
    set.Ico_union_Ico_eq_Ico hab hbc],
end

lemma Ico_union_Ico' {a b c d : α} (hcb : c ≤ b) (had : a ≤ d) :
  Ico a b ∪ Ico c d = Ico (min n l) (max m k) :=
by simp [←coe_inj, set.Ico_union_Ico' hlm hnk]

lemma union {a b c d : α} (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
  Ico a b ∪ Ico l k = Ico (min n l) (max m k) :=
by simp [←coe_inj, set.Ico_union_Ico h₁ h₂]

@[simp] lemma inter_consecutive (n m l : ℕ) : Ico a b ∩ Ico m l = ∅ :=
begin
  rw [← to_finset, ← to_finset, ← multiset.to_finset_inter, multiset.Ico.inter_consecutive],
  simp,
end

lemma inter {n m l k : ℕ} : Ico a b ∩ Ico l k = Ico (max n l) (min m k) :=
by simp [←coe_inj, ←inf_eq_min, ←sup_eq_max, set.Ico_inter_Ico]

lemma disjoint_consecutive (a b l : ℕ) : disjoint (Ico a b) (Ico m l) :=
le_of_eq $ inter_consecutive n m l

@[simp] theorem succ_singleton (n : ℕ) : Ico n (n+1) = {n} :=
eq_of_veq $ multiset.Ico.succ_singleton

theorem succ_top {n m : ℕ} (h : n ≤ m) : Ico n (m + 1) = insert m (Ico a b) :=
by rw [← to_finset, multiset.Ico.succ_top h, multiset.to_finset_cons, to_finset]

theorem succ_top' {n m : ℕ} (h : n < m) : Ico a b = insert (m - 1) (Ico n (m - 1)) :=
begin
  have w : m = m - 1 + 1 := (nat.sub_add_cancel (nat.one_le_of_lt h)).symm,
  conv { to_lhs, rw w },
  rw succ_top,
  exact nat.le_pred_of_lt h
end

theorem insert_succ_bot {n m : ℕ} (h : n < m) : insert n (Ico (n + 1) m) = Ico a b :=
by rw [eq_comm, ← to_finset, multiset.Ico.eq_cons h, multiset.to_finset_cons, to_finset]

@[simp] theorem pred_singleton {m : ℕ} (h : 0 < m) : Ico (m - 1) m = {m - 1} :=
eq_of_veq $ multiset.Ico.pred_singleton h

@[simp] theorem right_not_mem_Ico {a b : α} : b ∉ Ico a b :=
by { rw [mem_Ico, not_and], exact λ _, lt_irrefl _ }

lemma filter_lt_of_top_le {n m l : ℕ} (hml : m ≤ l) : (Ico a b).filter (λ x, x < l) = Ico a b :=
eq_of_veq $ multiset.Ico.filter_lt_of_top_le hml

lemma filter_lt_of_le_bot {n m l : ℕ} (hln : l ≤ n) : (Ico a b).filter (λ x, x < l) = ∅ :=
eq_of_veq $ multiset.Ico.filter_lt_of_le_bot hln

lemma filter_Ico_bot {n m : ℕ} (hnm : n < m) : (Ico a b).filter (λ x, x ≤ n) = {n} :=
eq_of_veq $ multiset.Ico.filter_le_of_bot hnm

lemma filter_lt_of_ge {n m l : ℕ} (hlm : l ≤ m) : (Ico a b).filter (λ x, x < l) = Ico n l :=
eq_of_veq $ multiset.Ico.filter_lt_of_ge hlm

@[simp] lemma filter_lt (n m l : ℕ) : (Ico a b).filter (λ x, x < l) = Ico n (min m l) :=
eq_of_veq $ multiset.Ico.filter_lt n m l

lemma filter_le_of_le_bot {n m l : ℕ} (hln : l ≤ n) : (Ico a b).filter (λ x, l ≤ x) = Ico a b :=
eq_of_veq $ multiset.Ico.filter_le_of_le_bot hln

lemma filter_le_of_top_le {n m l : ℕ} (hml : m ≤ l) : (Ico a b).filter (λ x, l ≤ x) = ∅ :=
eq_of_veq $ multiset.Ico.filter_le_of_top_le hml

lemma filter_le_of_le {n m l : ℕ} (hnl : n ≤ l) : (Ico a b).filter (λ x, l ≤ x) = Ico l m :=
eq_of_veq $ multiset.Ico.filter_le_of_le hnl

@[simp] lemma filter_le (n m l : ℕ) : (Ico a b).filter (λ x, l ≤ x) = Ico (max n l) m :=
eq_of_veq $ multiset.Ico.filter_le n m l

@[simp] lemma diff_left (l n m : ℕ) : (Ico a b) \ (Ico n l) = Ico (max n l) m :=
by ext k; by_cases n ≤ k; simp [h, and_comm]

@[simp] lemma diff_right (l n m : ℕ) : (Ico a b) \ (Ico l m) = Ico n (min m l) :=
have ∀k, (k < m ∧ (l ≤ k → m ≤ k)) ↔ (k < m ∧ k < l) :=
  assume k, and_congr_right $ assume hk, by rw [← not_imp_not]; simp [hk],
by ext k; by_cases n ≤ k; simp [h, this]

lemma image_const_sub {k m n : ℕ} (hkn : k ≤ n) :
  (Ico k m).image (λ j, n - j) = Ico (n + 1 - m) (n + 1 - k) :=
begin
  rw [nat.sub_add_comm hkn],
  ext j,
  simp only [mem, mem_image, exists_prop, nat.lt_iff_add_one_le, add_le_add_iff_right],
  split,
  { rintros ⟨j, ⟨hjk, hjm⟩, rfl⟩,
    split,
    { simp only [← nat.add_sub_add_right n 1 j, nat.sub_le_sub_left, hjm] },
    { exact nat.sub_le_sub_left _ hjk } },
  { rintros ⟨hm, hk⟩,
    have hj : j ≤ n := le_trans hk (nat.sub_le_self _ _),
    refine ⟨n - j, ⟨_, _⟩, _⟩,
    { apply nat.le_sub_right_of_add_le,
      rwa nat.le_sub_left_iff_add_le hkn at hk },
    { rwa [← nat.sub_add_comm hj, nat.sub_le_iff] },
    { exact nat.sub_sub_self hj } }
end

lemma range_eq_Ico (n : ℕ) : finset.range n = finset.Ico 0 n :=
by { ext i, simp }

lemma range_image_pred_top_sub (n : ℕ) :
  (finset.range n).image (λ j, n - 1 - j) = finset.range n :=
begin
  cases n,
  { simp },
  { simp [range_eq_Ico, Ico.image_const_sub] }
end

end finset
