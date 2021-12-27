/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.locally_finite

/-!
# Intervals as multisets

This file provides basic results about all the `multiset.Ixx`, which are defined in
`order.locally_finite`.
-/

variables {α : Type*}

namespace multiset
section preorder
variables [preorder α] [locally_finite_order α] {a b c : α}

lemma nodup_Icc : (Icc a b).nodup := finset.nodup _
lemma nodup_Ico : (Ico a b).nodup := finset.nodup _
lemma nodup_Ioc : (Ioc a b).nodup := finset.nodup _
lemma nodup_Ioo : (Ioo a b).nodup := finset.nodup _

@[simp] lemma Icc_eq_zero_iff : Icc a b = 0 ↔ ¬a ≤ b :=
by rw [Icc, finset.val_eq_zero, finset.Icc_eq_empty_iff]

@[simp] lemma Ico_eq_zero_iff : Ico a b = 0 ↔ ¬a < b :=
by rw [Ico, finset.val_eq_zero, finset.Ico_eq_empty_iff]

@[simp] lemma Ioc_eq_zero_iff : Ioc a b = 0 ↔ ¬a < b :=
by rw [Ioc, finset.val_eq_zero, finset.Ioc_eq_empty_iff]

@[simp] lemma Ioo_eq_zero_iff [densely_ordered α] : Ioo a b = 0 ↔ ¬a < b :=
by rw [Ioo, finset.val_eq_zero, finset.Ioo_eq_empty_iff]

alias Icc_eq_zero_iff ↔ _ multiset.Icc_eq_zero
alias Ico_eq_zero_iff ↔ _ multiset.Ico_eq_zero
alias Ioc_eq_zero_iff ↔ _ multiset.Ioc_eq_zero

@[simp] lemma Ioo_eq_zero (h : ¬a < b) : Ioo a b = 0 :=
eq_zero_iff_forall_not_mem.2 $ λ x hx, h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp] lemma Icc_eq_zero_of_lt (h : b < a) : Icc a b = 0 := Icc_eq_zero h.not_le
@[simp] lemma Ico_eq_zero_of_le (h : b ≤ a) : Ico a b = 0 := Ico_eq_zero h.not_lt
@[simp] lemma Ioc_eq_zero_of_le (h : b ≤ a) : Ioc a b = 0 := Ioc_eq_zero h.not_lt
@[simp] lemma Ioo_eq_zero_of_le (h : b ≤ a) : Ioo a b = 0 := Ioo_eq_zero h.not_lt

variables (a)

@[simp] lemma Ico_self : Ico a a = 0 := by rw [Ico, finset.Ico_self, finset.empty_val]
@[simp] lemma Ioc_self : Ioc a a = 0 := by rw [Ioc, finset.Ioc_self, finset.empty_val]
@[simp] lemma Ioo_self : Ioo a a = 0 := by rw [Ioo, finset.Ioo_self, finset.empty_val]

variables {a b c}

lemma left_mem_Icc : a ∈ Icc a b ↔ a ≤ b := finset.left_mem_Icc
lemma left_mem_Ico : a ∈ Ico a b ↔ a < b := finset.left_mem_Ico
lemma right_mem_Icc : b ∈ Icc a b ↔ a ≤ b := finset.right_mem_Icc
lemma right_mem_Ioc : b ∈ Ioc a b ↔ a < b := finset.right_mem_Ioc

@[simp] lemma left_not_mem_Ioc : a ∉ Ioc a b := finset.left_not_mem_Ioc
@[simp] lemma left_not_mem_Ioo : a ∉ Ioo a b := finset.left_not_mem_Ioo
@[simp] lemma right_not_mem_Ico : b ∉ Ico a b := finset.right_not_mem_Ico
@[simp] lemma right_not_mem_Ioo : b ∉ Ioo a b := finset.right_not_mem_Ioo

lemma Ico_filter_lt_of_le_left [decidable_pred (< c)] (hca : c ≤ a) :
  (Ico a b).filter (λ x, x < c) = ∅ :=
by { rw [Ico, ←finset.filter_val, finset.Ico_filter_lt_of_le_left hca], refl }

lemma Ico_filter_lt_of_right_le [decidable_pred (< c)] (hbc : b ≤ c) :
  (Ico a b).filter (λ x, x < c) = Ico a b :=
by rw [Ico, ←finset.filter_val, finset.Ico_filter_lt_of_right_le hbc]

lemma Ico_filter_lt_of_le_right [decidable_pred (< c)] (hcb : c ≤ b) :
  (Ico a b).filter (λ x, x < c) = Ico a c :=
by { rw [Ico, ←finset.filter_val, finset.Ico_filter_lt_of_le_right hcb], refl }

lemma Ico_filter_le_of_le_left [decidable_pred ((≤) c)] (hca : c ≤ a) :
  (Ico a b).filter (λ x, c ≤ x) = Ico a b :=
by rw [Ico, ←finset.filter_val, finset.Ico_filter_le_of_le_left hca]

lemma Ico_filter_le_of_right_le [decidable_pred ((≤) b)] :
  (Ico a b).filter (λ x, b ≤ x) = ∅ :=
by { rw [Ico, ←finset.filter_val, finset.Ico_filter_le_of_right_le], refl }

lemma Ico_filter_le_of_left_le [decidable_pred ((≤) c)] (hac : a ≤ c) :
  (Ico a b).filter (λ x, c ≤ x) = Ico c b :=
by { rw [Ico, ←finset.filter_val, finset.Ico_filter_le_of_left_le hac], refl }

end preorder

section partial_order
variables [partial_order α] [locally_finite_order α] {a b : α}

@[simp] lemma Icc_self (a : α) : Icc a a = {a} := by rw [Icc, finset.Icc_self, finset.singleton_val]

lemma Ico_cons_right (h : a ≤ b) : b ::ₘ (Ico a b) = Icc a b :=
by { classical,
  rw [Ico, ←finset.insert_val_of_not_mem right_not_mem_Ico, finset.Ico_insert_right h], refl }

lemma Ioo_cons_left (h : a < b) : a ::ₘ (Ioo a b) = Ico a b :=
by { classical,
  rw [Ioo, ←finset.insert_val_of_not_mem left_not_mem_Ioo, finset.Ioo_insert_left h], refl }

lemma Ico_disjoint_Ico {a b c d : α} (h : b ≤ c) : (Ico a b).disjoint (Ico c d) :=
λ x hab hbc, by { rw mem_Ico at hab hbc, exact hab.2.not_le (h.trans hbc.1) }

@[simp] lemma Ico_inter_Ico_of_le [decidable_eq α] {a b c d : α} (h : b ≤ c) :
  Ico a b ∩ Ico c d = 0 :=
multiset.inter_eq_zero_iff_disjoint.2 $ Ico_disjoint_Ico h

lemma Ico_filter_le_left {a b : α} [decidable_pred (≤ a)] (hab : a < b) :
  (Ico a b).filter (λ x, x ≤ a) = {a} :=
by { rw [Ico, ←finset.filter_val, finset.Ico_filter_le_left hab], refl }

lemma card_Ico_eq_card_Icc_sub_one (a b : α) : (Ico a b).card = (Icc a b).card - 1 :=
finset.card_Ico_eq_card_Icc_sub_one _ _

lemma card_Ioc_eq_card_Icc_sub_one (a b : α) : (Ioc a b).card = (Icc a b).card - 1 :=
finset.card_Ioc_eq_card_Icc_sub_one _ _

lemma card_Ioo_eq_card_Ico_sub_one (a b : α) : (Ioo a b).card = (Ico a b).card - 1 :=
finset.card_Ioo_eq_card_Ico_sub_one _ _

lemma card_Ioo_eq_card_Icc_sub_two (a b : α) : (Ioo a b).card = (Icc a b).card - 2 :=
finset.card_Ioo_eq_card_Icc_sub_two _ _

end partial_order

section linear_order
variables [linear_order α] [locally_finite_order α] {a b c d : α}

lemma Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) :
  Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
finset.Ico_subset_Ico_iff h

lemma Ico_add_Ico_eq_Ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
  Ico a b + Ico b c = Ico a c :=
by rw [add_eq_union_iff_disjoint.2 (Ico_disjoint_Ico le_rfl), Ico, Ico, Ico, ←finset.union_val,
  finset.Ico_union_Ico_eq_Ico hab hbc]

lemma Ico_inter_Ico : Ico a b ∩ Ico c d = Ico (max a c) (min b d) :=
by rw [Ico, Ico, Ico, ←finset.inter_val, finset.Ico_inter_Ico]

@[simp] lemma Ico_filter_lt (a b c : α) : (Ico a b).filter (λ x, x < c) = Ico a (min b c) :=
by rw [Ico, Ico, ←finset.filter_val, finset.Ico_filter_lt]

@[simp] lemma Ico_filter_le (a b c : α) : (Ico a b).filter (λ x, c ≤ x) = Ico (max a c) b :=
by rw [Ico, Ico, ←finset.filter_val, finset.Ico_filter_le]

@[simp] lemma Ico_sub_Ico_left (a b c : α) : Ico a b - Ico a c = Ico (max a c) b :=
by rw [Ico, Ico, Ico, ←finset.sdiff_val, finset.Ico_diff_Ico_left]

@[simp] lemma Ico_sub_Ico_right (a b c : α) : Ico a b - Ico c b = Ico a (min b c) :=
by rw [Ico, Ico, Ico, ←finset.sdiff_val, finset.Ico_diff_Ico_right]

end linear_order

section ordered_cancel_add_comm_monoid
variables [ordered_cancel_add_comm_monoid α] [has_exists_add_of_le α] [locally_finite_order α]

lemma map_add_left_Icc (a b c : α) : (Icc a b).map ((+) c) = Icc (c + a) (c + b) :=
by { classical, rw [Icc, Icc, ←finset.image_add_left_Icc, finset.image_val,
    (multiset.nodup_map (add_right_injective c) $ finset.nodup _).erase_dup] }

lemma map_add_left_Ico (a b c : α) : (Ico a b).map ((+) c) = Ico (c + a) (c + b) :=
by { classical, rw [Ico, Ico, ←finset.image_add_left_Ico, finset.image_val,
    (multiset.nodup_map (add_right_injective c) $ finset.nodup _).erase_dup] }

lemma map_add_left_Ioc (a b c : α) : (Ioc a b).map ((+) c) = Ioc (c + a) (c + b) :=
by { classical, rw [Ioc, Ioc, ←finset.image_add_left_Ioc, finset.image_val,
    (multiset.nodup_map (add_right_injective c) $ finset.nodup _).erase_dup] }

lemma map_add_left_Ioo (a b c : α) : (Ioo a b).map ((+) c) = Ioo (c + a) (c + b) :=
by { classical, rw [Ioo, Ioo, ←finset.image_add_left_Ioo, finset.image_val,
    (multiset.nodup_map (add_right_injective c) $ finset.nodup _).erase_dup] }

lemma map_add_right_Icc (a b c : α) : (Icc a b).map (λ x, x + c) = Icc (a + c) (b + c) :=
by { simp_rw add_comm _ c, exact map_add_left_Icc _ _ _ }

lemma map_add_right_Ico (a b c : α) : (Ico a b).map (λ x, x + c) = Ico (a + c) (b + c) :=
by { simp_rw add_comm _ c, exact map_add_left_Ico _ _ _ }

lemma map_add_right_Ioc (a b c : α) : (Ioc a b).map (λ x, x + c) = Ioc (a + c) (b + c) :=
by { simp_rw add_comm _ c, exact map_add_left_Ioc _ _ _ }

lemma map_add_right_Ioo (a b c : α) : (Ioo a b).map (λ x, x + c) = Ioo (a + c) (b + c) :=
by { simp_rw add_comm _ c, exact map_add_left_Ioo _ _ _ }

end ordered_cancel_add_comm_monoid
end multiset
