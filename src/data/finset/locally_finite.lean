/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yaël Dillies
-/
import order.locally_finite
import data.set.intervals.monoid

/-!
# Intervals as finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides basic results about all the `finset.Ixx`, which are defined in
`order.locally_finite`.

## TODO

This file was originally only about `finset.Ico a b` where `a b : ℕ`. No care has yet been taken to
generalize these lemmas properly and many lemmas about `Icc`, `Ioc`, `Ioo` are missing. In general,
what's to do is taking the lemmas in `data.x.intervals` and abstract away the concrete structure.

Complete the API. See
https://github.com/leanprover-community/mathlib/pull/14448#discussion_r906109235
for some ideas.
-/

open function order_dual
open_locale big_operators finset_interval

variables {ι α : Type*}

namespace finset
section preorder
variables [preorder α]

section locally_finite_order
variables [locally_finite_order α] {a a₁ a₂ b b₁ b₂ c x : α}

@[simp] lemma nonempty_Icc : (Icc a b).nonempty ↔ a ≤ b :=
by rw [←coe_nonempty, coe_Icc, set.nonempty_Icc]

@[simp] lemma nonempty_Ico : (Ico a b).nonempty ↔ a < b :=
by rw [←coe_nonempty, coe_Ico, set.nonempty_Ico]

@[simp] lemma nonempty_Ioc : (Ioc a b).nonempty ↔ a < b :=
by rw [←coe_nonempty, coe_Ioc, set.nonempty_Ioc]

@[simp] lemma nonempty_Ioo [densely_ordered α] : (Ioo a b).nonempty ↔ a < b :=
by rw [←coe_nonempty, coe_Ioo, set.nonempty_Ioo]

@[simp] lemma Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a ≤ b :=
by rw [←coe_eq_empty, coe_Icc, set.Icc_eq_empty_iff]

@[simp] lemma Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b :=
by rw [←coe_eq_empty, coe_Ico, set.Ico_eq_empty_iff]

@[simp] lemma Ioc_eq_empty_iff : Ioc a b = ∅ ↔ ¬a < b :=
by rw [←coe_eq_empty, coe_Ioc, set.Ioc_eq_empty_iff]

@[simp] lemma Ioo_eq_empty_iff [densely_ordered α] : Ioo a b = ∅ ↔ ¬a < b :=
by rw [←coe_eq_empty, coe_Ioo, set.Ioo_eq_empty_iff]

alias Icc_eq_empty_iff ↔ _ Icc_eq_empty
alias Ico_eq_empty_iff ↔ _ Ico_eq_empty
alias Ioc_eq_empty_iff ↔ _ Ioc_eq_empty

@[simp] lemma Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x hx, h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp] lemma Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅ := Icc_eq_empty h.not_le
@[simp] lemma Ico_eq_empty_of_le (h : b ≤ a) : Ico a b = ∅ := Ico_eq_empty h.not_lt
@[simp] lemma Ioc_eq_empty_of_le (h : b ≤ a) : Ioc a b = ∅ := Ioc_eq_empty h.not_lt
@[simp] lemma Ioo_eq_empty_of_le (h : b ≤ a) : Ioo a b = ∅ := Ioo_eq_empty h.not_lt

@[simp] lemma left_mem_Icc : a ∈ Icc a b ↔ a ≤ b := by simp only [mem_Icc, true_and, le_rfl]
@[simp] lemma left_mem_Ico : a ∈ Ico a b ↔ a < b := by simp only [mem_Ico, true_and, le_refl]
@[simp] lemma right_mem_Icc : b ∈ Icc a b ↔ a ≤ b := by simp only [mem_Icc, and_true, le_rfl]
@[simp] lemma right_mem_Ioc : b ∈ Ioc a b ↔ a < b := by simp only [mem_Ioc, and_true, le_rfl]

@[simp] lemma left_not_mem_Ioc : a ∉ Ioc a b := λ h, lt_irrefl _ (mem_Ioc.1 h).1
@[simp] lemma left_not_mem_Ioo : a ∉ Ioo a b := λ h, lt_irrefl _ (mem_Ioo.1 h).1
@[simp] lemma right_not_mem_Ico : b ∉ Ico a b := λ h, lt_irrefl _ (mem_Ico.1 h).2
@[simp] lemma right_not_mem_Ioo : b ∉ Ioo a b := λ h, lt_irrefl _ (mem_Ioo.1 h).2

lemma Icc_subset_Icc (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Icc a₁ b₁ ⊆ Icc a₂ b₂ :=
by simpa [←coe_subset] using set.Icc_subset_Icc ha hb

lemma Ico_subset_Ico (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ico a₁ b₁ ⊆ Ico a₂ b₂ :=
by simpa [←coe_subset] using set.Ico_subset_Ico ha hb

lemma Ioc_subset_Ioc (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ioc a₁ b₁ ⊆ Ioc a₂ b₂ :=
by simpa [←coe_subset] using set.Ioc_subset_Ioc ha hb

lemma Ioo_subset_Ioo (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ioo a₁ b₁ ⊆ Ioo a₂ b₂ :=
by simpa [←coe_subset] using set.Ioo_subset_Ioo ha hb

lemma Icc_subset_Icc_left (h : a₁ ≤ a₂) : Icc a₂ b ⊆ Icc a₁ b := Icc_subset_Icc h le_rfl
lemma Ico_subset_Ico_left (h : a₁ ≤ a₂) : Ico a₂ b ⊆ Ico a₁ b := Ico_subset_Ico h le_rfl
lemma Ioc_subset_Ioc_left (h : a₁ ≤ a₂) : Ioc a₂ b ⊆ Ioc a₁ b := Ioc_subset_Ioc h le_rfl
lemma Ioo_subset_Ioo_left (h : a₁ ≤ a₂) : Ioo a₂ b ⊆ Ioo a₁ b := Ioo_subset_Ioo h le_rfl
lemma Icc_subset_Icc_right (h : b₁ ≤ b₂) : Icc a b₁ ⊆ Icc a b₂ := Icc_subset_Icc le_rfl h
lemma Ico_subset_Ico_right (h : b₁ ≤ b₂) : Ico a b₁ ⊆ Ico a b₂ := Ico_subset_Ico le_rfl h
lemma Ioc_subset_Ioc_right (h : b₁ ≤ b₂) : Ioc a b₁ ⊆ Ioc a b₂ := Ioc_subset_Ioc le_rfl h
lemma Ioo_subset_Ioo_right (h : b₁ ≤ b₂) : Ioo a b₁ ⊆ Ioo a b₂ := Ioo_subset_Ioo le_rfl h

lemma Ico_subset_Ioo_left (h : a₁ < a₂) : Ico a₂ b ⊆ Ioo a₁ b :=
by { rw [←coe_subset, coe_Ico, coe_Ioo], exact set.Ico_subset_Ioo_left h }

lemma Ioc_subset_Ioo_right (h : b₁ < b₂) : Ioc a b₁ ⊆ Ioo a b₂ :=
by { rw [←coe_subset, coe_Ioc, coe_Ioo], exact set.Ioc_subset_Ioo_right h }

lemma Icc_subset_Ico_right (h : b₁ < b₂) : Icc a b₁ ⊆ Ico a b₂ :=
by { rw [←coe_subset, coe_Icc, coe_Ico], exact set.Icc_subset_Ico_right h }

lemma Ioo_subset_Ico_self : Ioo a b ⊆ Ico a b :=
by { rw [←coe_subset, coe_Ioo, coe_Ico], exact set.Ioo_subset_Ico_self }

lemma Ioo_subset_Ioc_self : Ioo a b ⊆ Ioc a b :=
by { rw [←coe_subset, coe_Ioo, coe_Ioc], exact set.Ioo_subset_Ioc_self }

lemma Ico_subset_Icc_self : Ico a b ⊆ Icc a b :=
by { rw [←coe_subset, coe_Ico, coe_Icc], exact set.Ico_subset_Icc_self }

lemma Ioc_subset_Icc_self : Ioc a b ⊆ Icc a b :=
by { rw [←coe_subset, coe_Ioc, coe_Icc], exact set.Ioc_subset_Icc_self }

lemma Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b := Ioo_subset_Ico_self.trans Ico_subset_Icc_self

lemma Icc_subset_Icc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
by rw [←coe_subset, coe_Icc, coe_Icc, set.Icc_subset_Icc_iff h₁]

lemma Icc_subset_Ioo_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ :=
by rw [←coe_subset, coe_Icc, coe_Ioo, set.Icc_subset_Ioo_iff h₁]

lemma Icc_subset_Ico_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ < b₂ :=
by rw [←coe_subset, coe_Icc, coe_Ico, set.Icc_subset_Ico_iff h₁]

lemma Icc_subset_Ioc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ ≤ b₂ :=
(Icc_subset_Ico_iff h₁.dual).trans and.comm

--TODO: `Ico_subset_Ioo_iff`, `Ioc_subset_Ioo_iff`

lemma Icc_ssubset_Icc_left (hI : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) : Icc a₁ b₁ ⊂ Icc a₂ b₂ :=
by { rw [←coe_ssubset, coe_Icc, coe_Icc], exact set.Icc_ssubset_Icc_left hI ha hb }

lemma Icc_ssubset_Icc_right (hI : a₂ ≤ b₂) (ha : a₂ ≤ a₁) (hb : b₁ < b₂) : Icc a₁ b₁ ⊂ Icc a₂ b₂ :=
by { rw [←coe_ssubset, coe_Icc, coe_Icc], exact set.Icc_ssubset_Icc_right hI ha hb }

variables (a)

@[simp] lemma Ico_self : Ico a a = ∅ := Ico_eq_empty $ lt_irrefl _
@[simp] lemma Ioc_self : Ioc a a = ∅ := Ioc_eq_empty $ lt_irrefl _
@[simp] lemma Ioo_self : Ioo a a = ∅ := Ioo_eq_empty $ lt_irrefl _

variables {a}

/-- A set with upper and lower bounds in a locally finite order is a fintype -/
def _root_.set.fintype_of_mem_bounds {s : set α} [decidable_pred (∈ s)]
  (ha : a ∈ lower_bounds s) (hb : b ∈ upper_bounds s) : fintype s :=
set.fintype_subset (set.Icc a b) $ λ x hx, ⟨ha hx, hb hx⟩

lemma _root_.bdd_below.finite_of_bdd_above {s : set α} (h₀ : bdd_below s) (h₁ : bdd_above s) :
  s.finite :=
let ⟨a, ha⟩ := h₀, ⟨b, hb⟩ := h₁ in by { classical, exact ⟨set.fintype_of_mem_bounds ha hb⟩ }

section filter

lemma Ico_filter_lt_of_le_left [decidable_pred (< c)] (hca : c ≤ a) : (Ico a b).filter (< c) = ∅ :=
filter_false_of_mem (λ x hx, (hca.trans (mem_Ico.1 hx).1).not_lt)

lemma Ico_filter_lt_of_right_le [decidable_pred (< c)] (hbc : b ≤ c) :
  (Ico a b).filter (< c) = Ico a b :=
filter_true_of_mem (λ x hx, (mem_Ico.1 hx).2.trans_le hbc)

lemma Ico_filter_lt_of_le_right [decidable_pred (< c)] (hcb : c ≤ b) :
  (Ico a b).filter (< c) = Ico a c :=
begin
  ext x,
  rw [mem_filter, mem_Ico, mem_Ico, and.right_comm],
  exact and_iff_left_of_imp (λ h, h.2.trans_le hcb),
end

lemma Ico_filter_le_of_le_left {a b c : α} [decidable_pred ((≤) c)] (hca : c ≤ a) :
  (Ico a b).filter ((≤) c) = Ico a b :=
filter_true_of_mem (λ x hx, hca.trans (mem_Ico.1 hx).1)

lemma Ico_filter_le_of_right_le {a b : α} [decidable_pred ((≤) b)] : (Ico a b).filter ((≤) b) = ∅ :=
filter_false_of_mem (λ x hx, (mem_Ico.1 hx).2.not_le)

lemma Ico_filter_le_of_left_le {a b c : α} [decidable_pred ((≤) c)] (hac : a ≤ c) :
  (Ico a b).filter ((≤) c) = Ico c b :=
begin
  ext x,
  rw [mem_filter, mem_Ico, mem_Ico, and_comm, and.left_comm],
  exact and_iff_right_of_imp (λ h, hac.trans h.1),
end

lemma Icc_filter_lt_of_lt_right {a b c : α} [decidable_pred (< c)] (h : b < c) :
  (Icc a b).filter (< c) = Icc a b :=
(finset.filter_eq_self _).2 (λ x hx, lt_of_le_of_lt (mem_Icc.1 hx).2 h)

lemma Ioc_filter_lt_of_lt_right {a b c : α} [decidable_pred (< c)] (h : b < c) :
  (Ioc a b).filter (< c) = Ioc a b :=
(finset.filter_eq_self _).2 (λ x hx, lt_of_le_of_lt (mem_Ioc.1 hx).2 h)

lemma Iic_filter_lt_of_lt_right {α} [preorder α] [locally_finite_order_bot α]
    {a c : α} [decidable_pred (< c)] (h : a < c) :
  (Iic a).filter (< c) = Iic a :=
(finset.filter_eq_self _).2 (λ x hx, lt_of_le_of_lt (mem_Iic.1 hx) h)

variables (a b) [fintype α]

lemma filter_lt_lt_eq_Ioo [decidable_pred (λ j, a < j ∧ j < b)] :
  univ.filter (λ j, a < j ∧ j < b) = Ioo a b := by { ext, simp }

lemma filter_lt_le_eq_Ioc [decidable_pred (λ j, a < j ∧ j ≤ b)] :
  univ.filter (λ j, a < j ∧ j ≤ b) = Ioc a b := by { ext, simp }

lemma filter_le_lt_eq_Ico [decidable_pred (λ j, a ≤ j ∧ j < b)] :
  univ.filter (λ j, a ≤ j ∧ j < b) = Ico a b := by { ext, simp }

lemma filter_le_le_eq_Icc [decidable_pred (λ j, a ≤ j ∧ j ≤ b)] :
  univ.filter (λ j, a ≤ j ∧ j ≤ b) = Icc a b := by { ext, simp }

end filter

section locally_finite_order_top
variables [locally_finite_order_top α]

lemma Icc_subset_Ici_self : Icc a b ⊆ Ici a := by simpa [←coe_subset] using set.Icc_subset_Ici_self
lemma Ico_subset_Ici_self : Ico a b ⊆ Ici a := by simpa [←coe_subset] using set.Ico_subset_Ici_self
lemma Ioc_subset_Ioi_self : Ioc a b ⊆ Ioi a := by simpa [←coe_subset] using set.Ioc_subset_Ioi_self
lemma Ioo_subset_Ioi_self : Ioo a b ⊆ Ioi a := by simpa [←coe_subset] using set.Ioo_subset_Ioi_self
lemma Ioc_subset_Ici_self : Ioc a b ⊆ Ici a := Ioc_subset_Icc_self.trans Icc_subset_Ici_self
lemma Ioo_subset_Ici_self : Ioo a b ⊆ Ici a := Ioo_subset_Ico_self.trans Ico_subset_Ici_self

end locally_finite_order_top

section locally_finite_order_bot
variables [locally_finite_order_bot α]

lemma Icc_subset_Iic_self : Icc a b ⊆ Iic b := by simpa [←coe_subset] using set.Icc_subset_Iic_self
lemma Ioc_subset_Iic_self : Ioc a b ⊆ Iic b := by simpa [←coe_subset] using set.Ioc_subset_Iic_self
lemma Ico_subset_Iio_self : Ico a b ⊆ Iio b := by simpa [←coe_subset] using set.Ico_subset_Iio_self
lemma Ioo_subset_Iio_self : Ioo a b ⊆ Iio b := by simpa [←coe_subset] using set.Ioo_subset_Iio_self
lemma Ico_subset_Iic_self : Ico a b ⊆ Iic b := Ico_subset_Icc_self.trans Icc_subset_Iic_self
lemma Ioo_subset_Iic_self : Ioo a b ⊆ Iic b := Ioo_subset_Ioc_self.trans Ioc_subset_Iic_self

end locally_finite_order_bot
end locally_finite_order

section locally_finite_order_top
variables [locally_finite_order_top α] {a : α}

lemma Ioi_subset_Ici_self : Ioi a ⊆ Ici a := by simpa [←coe_subset] using set.Ioi_subset_Ici_self

lemma _root_.bdd_below.finite {s : set α} (hs : bdd_below s) : s.finite :=
let ⟨a, ha⟩ := hs in (Ici a).finite_to_set.subset $ λ x hx, mem_Ici.2 $ ha hx

variables [fintype α]

lemma filter_lt_eq_Ioi [decidable_pred ((<) a)] : univ.filter ((<) a) = Ioi a := by { ext, simp }
lemma filter_le_eq_Ici [decidable_pred ((≤) a)] : univ.filter ((≤) a) = Ici a := by { ext, simp }

end locally_finite_order_top

section locally_finite_order_bot
variables [locally_finite_order_bot α] {a : α}

lemma Iio_subset_Iic_self : Iio a ⊆ Iic a := by simpa [←coe_subset] using set.Iio_subset_Iic_self

lemma _root_.bdd_above.finite {s : set α} (hs : bdd_above s) : s.finite := hs.dual.finite

variables [fintype α]

lemma filter_gt_eq_Iio [decidable_pred (< a)] : univ.filter (< a) = Iio a := by { ext, simp }
lemma filter_ge_eq_Iic [decidable_pred (≤ a)] : univ.filter (≤ a) = Iic a := by { ext, simp }

end locally_finite_order_bot

variables [locally_finite_order_top α] [locally_finite_order_bot α]

lemma disjoint_Ioi_Iio (a : α) :  disjoint (Ioi a) (Iio a) :=
disjoint_left.2 $ λ b hab hba, (mem_Ioi.1 hab).not_lt $ mem_Iio.1 hba

end preorder

section partial_order
variables [partial_order α] [locally_finite_order α] {a b c : α}

@[simp] lemma Icc_self (a : α) : Icc a a = {a} := by rw [←coe_eq_singleton, coe_Icc, set.Icc_self]

@[simp] lemma Icc_eq_singleton_iff : Icc a b = {c} ↔ a = c ∧ b = c :=
by rw [←coe_eq_singleton, coe_Icc, set.Icc_eq_singleton_iff]

lemma Ico_disjoint_Ico_consecutive (a b c : α) : disjoint (Ico a b) (Ico b c) :=
disjoint_left.2 $ λ x hab hbc, (mem_Ico.mp hab).2.not_le (mem_Ico.mp hbc).1

section decidable_eq
variables [decidable_eq α]

@[simp] lemma Icc_erase_left (a b : α) : (Icc a b).erase a = Ioc a b := by simp [←coe_inj]
@[simp] lemma Icc_erase_right (a b : α) : (Icc a b).erase b = Ico a b := by simp [←coe_inj]
@[simp] lemma Ico_erase_left (a b : α) : (Ico a b).erase a = Ioo a b := by simp [←coe_inj]
@[simp] lemma Ioc_erase_right (a b : α) : (Ioc a b).erase b = Ioo a b := by simp [←coe_inj]
@[simp] lemma Icc_diff_both (a b : α) : Icc a b \ {a, b} = Ioo a b := by simp [←coe_inj]

@[simp] lemma Ico_insert_right (h : a ≤ b) : insert b (Ico a b) = Icc a b :=
by rw [←coe_inj, coe_insert, coe_Icc, coe_Ico, set.insert_eq, set.union_comm, set.Ico_union_right h]

@[simp] lemma Ioc_insert_left (h : a ≤ b) : insert a (Ioc a b) = Icc a b :=
by rw [←coe_inj, coe_insert, coe_Ioc, coe_Icc, set.insert_eq, set.union_comm, set.Ioc_union_left h]

@[simp] lemma Ioo_insert_left (h : a < b) : insert a (Ioo a b) = Ico a b :=
by rw [←coe_inj, coe_insert, coe_Ioo, coe_Ico, set.insert_eq, set.union_comm, set.Ioo_union_left h]

@[simp] lemma Ioo_insert_right (h : a < b) : insert b (Ioo a b) = Ioc a b :=
by rw [←coe_inj, coe_insert, coe_Ioo, coe_Ioc, set.insert_eq, set.union_comm, set.Ioo_union_right h]

@[simp] lemma Icc_diff_Ico_self (h : a ≤ b) : Icc a b \ Ico a b = {b} := by simp [←coe_inj, h]
@[simp] lemma Icc_diff_Ioc_self (h : a ≤ b) : Icc a b \ Ioc a b = {a} := by simp [←coe_inj, h]
@[simp] lemma Icc_diff_Ioo_self (h : a ≤ b) : Icc a b \ Ioo a b = {a, b} := by simp [←coe_inj, h]
@[simp] lemma Ico_diff_Ioo_self (h : a < b) : Ico a b \ Ioo a b = {a} := by simp [←coe_inj, h]
@[simp] lemma Ioc_diff_Ioo_self (h : a < b) : Ioc a b \ Ioo a b = {b} := by simp [←coe_inj, h]

@[simp] lemma Ico_inter_Ico_consecutive (a b c : α) : Ico a b ∩ Ico b c = ∅ :=
(Ico_disjoint_Ico_consecutive a b c).eq_bot

end decidable_eq

-- Those lemmas are purposefully the other way around

/-- `finset.cons` version of `finset.Ico_insert_right`. -/
lemma Icc_eq_cons_Ico (h : a ≤ b) : Icc a b = (Ico a b).cons b right_not_mem_Ico :=
by { classical, rw [cons_eq_insert, Ico_insert_right h] }

/-- `finset.cons` version of `finset.Ioc_insert_left`. -/
lemma Icc_eq_cons_Ioc (h : a ≤ b) : Icc a b = (Ioc a b).cons a left_not_mem_Ioc :=
by { classical, rw [cons_eq_insert, Ioc_insert_left h] }

/-- `finset.cons` version of `finset.Ioo_insert_right`. -/
lemma Ioc_eq_cons_Ioo (h : a < b) : Ioc a b = (Ioo a b).cons b right_not_mem_Ioo :=
by { classical, rw [cons_eq_insert, Ioo_insert_right h], }

/-- `finset.cons` version of `finset.Ioo_insert_left`. -/
lemma Ico_eq_cons_Ioo (h : a < b) : Ico a b = (Ioo a b).cons a left_not_mem_Ioo :=
by { classical, rw [cons_eq_insert, Ioo_insert_left h] }

lemma Ico_filter_le_left {a b : α} [decidable_pred (≤ a)] (hab : a < b) :
  (Ico a b).filter (λ x, x ≤ a) = {a} :=
begin
  ext x,
  rw [mem_filter, mem_Ico, mem_singleton, and.right_comm, ←le_antisymm_iff, eq_comm],
  exact and_iff_left_of_imp (λ h, h.le.trans_lt hab),
end

lemma card_Ico_eq_card_Icc_sub_one (a b : α) : (Ico a b).card = (Icc a b).card - 1 :=
begin
  classical,
  by_cases h : a ≤ b,
  { rw [Icc_eq_cons_Ico h, card_cons],
    exact (nat.add_sub_cancel _ _).symm },
  { rw [Ico_eq_empty (λ h', h h'.le), Icc_eq_empty h, card_empty, zero_tsub] }
end

lemma card_Ioc_eq_card_Icc_sub_one (a b : α) : (Ioc a b).card = (Icc a b).card - 1 :=
@card_Ico_eq_card_Icc_sub_one αᵒᵈ _ _ _ _

lemma card_Ioo_eq_card_Ico_sub_one (a b : α) : (Ioo a b).card = (Ico a b).card - 1 :=
begin
  classical,
  by_cases h : a < b,
  { rw [Ico_eq_cons_Ioo h, card_cons],
    exact (nat.add_sub_cancel _ _).symm },
  { rw [Ioo_eq_empty h, Ico_eq_empty h, card_empty, zero_tsub] }
end

lemma card_Ioo_eq_card_Ioc_sub_one (a b : α) : (Ioo a b).card = (Ioc a b).card - 1 :=
@card_Ioo_eq_card_Ico_sub_one αᵒᵈ _ _ _ _

lemma card_Ioo_eq_card_Icc_sub_two (a b : α) : (Ioo a b).card = (Icc a b).card - 2 :=
by { rw [card_Ioo_eq_card_Ico_sub_one, card_Ico_eq_card_Icc_sub_one], refl }

end partial_order

section bounded_partial_order
variables [partial_order α]

section order_top
variables [locally_finite_order_top α]

@[simp] lemma Ici_erase [decidable_eq α] (a : α) : (Ici a).erase a = Ioi a :=
by { ext, simp_rw [finset.mem_erase, mem_Ici, mem_Ioi, lt_iff_le_and_ne, and_comm, ne_comm], }
@[simp] lemma Ioi_insert [decidable_eq α] (a : α) : insert a (Ioi a) = Ici a :=
by { ext, simp_rw [finset.mem_insert, mem_Ici, mem_Ioi, le_iff_lt_or_eq, or_comm, eq_comm] }

@[simp] lemma not_mem_Ioi_self {b : α} : b ∉ Ioi b := λ h, lt_irrefl _ (mem_Ioi.1 h)

-- Purposefully written the other way around
/-- `finset.cons` version of `finset.Ioi_insert`. -/
lemma Ici_eq_cons_Ioi (a : α) : Ici a = (Ioi a).cons a not_mem_Ioi_self :=
by { classical, rw [cons_eq_insert, Ioi_insert] }

lemma card_Ioi_eq_card_Ici_sub_one (a : α) : (Ioi a).card = (Ici a).card - 1 :=
by rw [Ici_eq_cons_Ioi, card_cons, add_tsub_cancel_right]

end order_top

section order_bot
variables [locally_finite_order_bot α]

@[simp] lemma Iic_erase [decidable_eq α] (b : α) : (Iic b).erase b = Iio b :=
by { ext, simp_rw [finset.mem_erase, mem_Iic, mem_Iio, lt_iff_le_and_ne, and_comm] }
@[simp] lemma Iio_insert [decidable_eq α] (b : α) : insert b (Iio b) = Iic b :=
by { ext, simp_rw [finset.mem_insert, mem_Iic, mem_Iio, le_iff_lt_or_eq, or_comm] }

@[simp] lemma not_mem_Iio_self {b : α} : b ∉ Iio b := λ h, lt_irrefl _ (mem_Iio.1 h)

-- Purposefully written the other way around
/-- `finset.cons` version of `finset.Iio_insert`. -/
lemma Iic_eq_cons_Iio (b : α) : Iic b = (Iio b).cons b not_mem_Iio_self :=
by { classical, rw [cons_eq_insert, Iio_insert] }

lemma card_Iio_eq_card_Iic_sub_one (a : α) : (Iio a).card = (Iic a).card - 1 :=
by rw [Iic_eq_cons_Iio, card_cons, add_tsub_cancel_right]

end order_bot

end bounded_partial_order

section linear_order
variables [linear_order α]

section locally_finite_order
variables [locally_finite_order α] {a b : α}

lemma Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) :
  Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
by rw [←coe_subset, coe_Ico, coe_Ico, set.Ico_subset_Ico_iff h]

lemma Ico_union_Ico_eq_Ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
  Ico a b ∪ Ico b c = Ico a c :=
by rw [←coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, set.Ico_union_Ico_eq_Ico hab hbc]

@[simp] lemma Ioc_union_Ioc_eq_Ioc {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) :
  Ioc a b ∪ Ioc b c = Ioc a c :=
by rw [←coe_inj, coe_union, coe_Ioc, coe_Ioc, coe_Ioc, set.Ioc_union_Ioc_eq_Ioc h₁ h₂]

lemma Ico_subset_Ico_union_Ico {a b c : α} :
  Ico a c ⊆ Ico a b ∪ Ico b c :=
by { rw [←coe_subset, coe_union, coe_Ico, coe_Ico, coe_Ico], exact set.Ico_subset_Ico_union_Ico }

lemma Ico_union_Ico' {a b c d : α} (hcb : c ≤ b) (had : a ≤ d) :
  Ico a b ∪ Ico c d = Ico (min a c) (max b d) :=
by rw [←coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, set.Ico_union_Ico' hcb had]

lemma Ico_union_Ico {a b c d : α} (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
  Ico a b ∪ Ico c d = Ico (min a c) (max b d) :=
by rw [←coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, set.Ico_union_Ico h₁ h₂]

lemma Ico_inter_Ico {a b c d : α} : Ico a b ∩ Ico c d = Ico (max a c) (min b d) :=
by rw [←coe_inj, coe_inter, coe_Ico, coe_Ico, coe_Ico, ←inf_eq_min, ←sup_eq_max, set.Ico_inter_Ico]

@[simp] lemma Ico_filter_lt (a b c : α) : (Ico a b).filter (λ x, x < c) = Ico a (min b c) :=
begin
  cases le_total b c,
  { rw [Ico_filter_lt_of_right_le h, min_eq_left h] },
  { rw [Ico_filter_lt_of_le_right h, min_eq_right h] }
end

@[simp] lemma Ico_filter_le (a b c : α) : (Ico a b).filter (λ x, c ≤ x) = Ico (max a c) b :=
begin
  cases le_total a c,
  { rw [Ico_filter_le_of_left_le h, max_eq_right h] },
  { rw [Ico_filter_le_of_le_left h, max_eq_left h] }
end

@[simp] lemma Ioo_filter_lt (a b c : α) : (Ioo a b).filter (< c) = Ioo a (min b c) :=
by { ext, simp [and_assoc] }

@[simp] lemma Iio_filter_lt {α} [linear_order α] [locally_finite_order_bot α] (a b : α) :
  (Iio a).filter (< b) = Iio (min a b) :=
by { ext, simp [and_assoc] }

@[simp] lemma Ico_diff_Ico_left (a b c : α) : (Ico a b) \ (Ico a c) = Ico (max a c) b :=
begin
  cases le_total a c,
  { ext x,
    rw [mem_sdiff, mem_Ico, mem_Ico, mem_Ico, max_eq_right h, and.right_comm, not_and, not_lt],
    exact and_congr_left' ⟨λ hx, hx.2 hx.1, λ hx, ⟨h.trans hx, λ _, hx⟩⟩ },
  { rw [Ico_eq_empty_of_le h, sdiff_empty, max_eq_left h] }
end

@[simp] lemma Ico_diff_Ico_right (a b c : α) : (Ico a b) \ (Ico c b) = Ico a (min b c) :=
begin
  cases le_total b c,
  { rw [Ico_eq_empty_of_le h, sdiff_empty, min_eq_left h] },
  { ext x,
    rw [mem_sdiff, mem_Ico, mem_Ico, mem_Ico, min_eq_right h, and_assoc, not_and', not_le],
    exact and_congr_right' ⟨λ hx, hx.2 hx.1, λ hx, ⟨hx.trans_le h, λ _, hx⟩⟩ }
end

end locally_finite_order

variables [fintype α] [locally_finite_order_top α] [locally_finite_order_bot α]

lemma Ioi_disj_union_Iio (a : α) :
  (Ioi a).disj_union (Iio a) (disjoint_Ioi_Iio a) = ({a} : finset α)ᶜ :=
by { ext, simp [eq_comm] }

end linear_order

section lattice
variables [lattice α] [locally_finite_order α] {a a₁ a₂ b b₁ b₂ c x : α}

lemma uIcc_to_dual (a b : α) : [to_dual a, to_dual b] = [a, b].map to_dual.to_embedding :=
Icc_to_dual _ _

@[simp] lemma uIcc_of_le (h : a ≤ b) : [a, b] = Icc a b :=
by rw [uIcc, inf_eq_left.2 h, sup_eq_right.2 h]

@[simp] lemma uIcc_of_ge (h : b ≤ a) : [a, b] = Icc b a :=
by rw [uIcc, inf_eq_right.2 h, sup_eq_left.2 h]

lemma uIcc_comm (a b : α) : [a, b] = [b, a] := by rw [uIcc, uIcc, inf_comm, sup_comm]

@[simp] lemma uIcc_self : [a, a] = {a} := by simp [uIcc]

@[simp] lemma nonempty_uIcc : finset.nonempty [a, b] := nonempty_Icc.2 inf_le_sup

lemma Icc_subset_uIcc : Icc a b ⊆ [a, b] := Icc_subset_Icc inf_le_left le_sup_right
lemma Icc_subset_uIcc' : Icc b a ⊆ [a, b] := Icc_subset_Icc inf_le_right le_sup_left

@[simp] lemma left_mem_uIcc : a ∈ [a, b] := mem_Icc.2 ⟨inf_le_left, le_sup_left⟩
@[simp] lemma right_mem_uIcc : b ∈ [a, b] := mem_Icc.2 ⟨inf_le_right, le_sup_right⟩

lemma mem_uIcc_of_le (ha : a ≤ x) (hb : x ≤ b) : x ∈ [a, b] := Icc_subset_uIcc $ mem_Icc.2 ⟨ha, hb⟩
lemma mem_uIcc_of_ge (hb : b ≤ x) (ha : x ≤ a) : x ∈ [a, b] := Icc_subset_uIcc' $ mem_Icc.2 ⟨hb, ha⟩

lemma uIcc_subset_uIcc (h₁ : a₁ ∈ [a₂, b₂]) (h₂ : b₁ ∈ [a₂, b₂]) : [a₁, b₁] ⊆ [a₂, b₂] :=
by { rw mem_uIcc at h₁ h₂, exact Icc_subset_Icc (le_inf h₁.1 h₂.1) (sup_le h₁.2 h₂.2) }

lemma uIcc_subset_Icc (ha : a₁ ∈ Icc a₂ b₂) (hb : b₁ ∈ Icc a₂ b₂) : [a₁, b₁] ⊆ Icc a₂ b₂ :=
by { rw mem_Icc at ha hb, exact Icc_subset_Icc (le_inf ha.1 hb.1) (sup_le ha.2 hb.2) }

lemma uIcc_subset_uIcc_iff_mem : [a₁, b₁] ⊆ [a₂, b₂] ↔ a₁ ∈ [a₂, b₂] ∧ b₁ ∈ [a₂, b₂] :=
⟨λ h, ⟨h left_mem_uIcc, h right_mem_uIcc⟩, λ h, uIcc_subset_uIcc h.1 h.2⟩

lemma uIcc_subset_uIcc_iff_le' : [a₁, b₁] ⊆ [a₂, b₂] ↔ a₂ ⊓ b₂ ≤ a₁ ⊓ b₁ ∧ a₁ ⊔ b₁ ≤ a₂ ⊔ b₂ :=
Icc_subset_Icc_iff inf_le_sup

lemma uIcc_subset_uIcc_right (h : x ∈ [a, b]) : [x, b] ⊆ [a, b] := uIcc_subset_uIcc h right_mem_uIcc
lemma uIcc_subset_uIcc_left (h : x ∈ [a, b]) : [a, x] ⊆ [a, b] := uIcc_subset_uIcc left_mem_uIcc h

end lattice

section distrib_lattice
variables [distrib_lattice α] [locally_finite_order α] {a a₁ a₂ b b₁ b₂ c x : α}

lemma eq_of_mem_uIcc_of_mem_uIcc : a ∈ [b, c] → b ∈ [a, c] → a = b :=
by { simp_rw mem_uIcc, exact set.eq_of_mem_uIcc_of_mem_uIcc }

lemma eq_of_mem_uIcc_of_mem_uIcc' : b ∈ [a, c] → c ∈ [a, b] → b = c :=
by { simp_rw mem_uIcc, exact set.eq_of_mem_uIcc_of_mem_uIcc' }

lemma uIcc_injective_right (a : α) : injective (λ b, [b, a]) :=
λ b c h, by { rw ext_iff at h,
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc) }

lemma uIcc_injective_left (a : α) : injective (uIcc a) :=
by simpa only [uIcc_comm] using uIcc_injective_right a

end distrib_lattice

section linear_order
variables [linear_order α] [locally_finite_order α] {a a₁ a₂ b b₁ b₂ c x : α}

lemma Icc_min_max : Icc (min a b) (max a b) = [a, b] := rfl

lemma uIcc_of_not_le (h : ¬ a ≤ b) : [a, b] = Icc b a := uIcc_of_ge $ le_of_not_ge h
lemma uIcc_of_not_ge (h : ¬ b ≤ a) : [a, b] = Icc a b := uIcc_of_le $ le_of_not_ge h

lemma uIcc_eq_union : [a, b] = Icc a b ∪ Icc b a :=
coe_injective $ by { push_cast, exact set.uIcc_eq_union }

lemma mem_uIcc' : a ∈ [b, c] ↔ b ≤ a ∧ a ≤ c ∨ c ≤ a ∧ a ≤ b := by simp [uIcc_eq_union]

lemma not_mem_uIcc_of_lt : c < a → c < b → c ∉ [a, b] :=
by { rw mem_uIcc, exact set.not_mem_uIcc_of_lt }

lemma not_mem_uIcc_of_gt : a < c → b < c → c ∉ [a, b] :=
by { rw mem_uIcc, exact set.not_mem_uIcc_of_gt }

lemma uIcc_subset_uIcc_iff_le :
  [a₁, b₁] ⊆ [a₂, b₂] ↔ min a₂ b₂ ≤ min a₁ b₁ ∧ max a₁ b₁ ≤ max a₂ b₂ :=
uIcc_subset_uIcc_iff_le'

/-- A sort of triangle inequality. -/
lemma uIcc_subset_uIcc_union_uIcc : [a, c] ⊆ [a, b] ∪ [b, c] :=
coe_subset.1 $ by { push_cast, exact set.uIcc_subset_uIcc_union_uIcc }

end linear_order

section ordered_cancel_add_comm_monoid
variables [ordered_cancel_add_comm_monoid α] [has_exists_add_of_le α] [locally_finite_order α]

@[simp] lemma map_add_left_Icc (a b c : α) :
  (Icc a b).map (add_left_embedding c) = Icc (c + a) (c + b) :=
by { rw [← coe_inj, coe_map, coe_Icc, coe_Icc], exact set.image_const_add_Icc _ _ _ }

@[simp] lemma map_add_right_Icc (a b c : α) :
  (Icc a b).map (add_right_embedding c) = Icc (a + c) (b + c) :=
by { rw [← coe_inj, coe_map, coe_Icc, coe_Icc], exact set.image_add_const_Icc _ _ _ }

@[simp] lemma map_add_left_Ico (a b c : α) :
  (Ico a b).map (add_left_embedding c) = Ico (c + a) (c + b) :=
by { rw [← coe_inj, coe_map, coe_Ico, coe_Ico], exact set.image_const_add_Ico _ _ _ }

@[simp] lemma map_add_right_Ico (a b c : α) :
  (Ico a b).map (add_right_embedding c) = Ico (a + c) (b + c) :=
by { rw [← coe_inj, coe_map, coe_Ico, coe_Ico], exact set.image_add_const_Ico _ _ _ }

@[simp] lemma map_add_left_Ioc (a b c : α) :
  (Ioc a b).map (add_left_embedding c) = Ioc (c + a) (c + b) :=
by { rw [← coe_inj, coe_map, coe_Ioc, coe_Ioc], exact set.image_const_add_Ioc _ _ _ }

@[simp] lemma map_add_right_Ioc (a b c : α) :
  (Ioc a b).map (add_right_embedding c) = Ioc (a + c) (b + c) :=
by { rw [← coe_inj, coe_map, coe_Ioc, coe_Ioc], exact set.image_add_const_Ioc _ _ _ }

@[simp] lemma map_add_left_Ioo (a b c : α) :
  (Ioo a b).map (add_left_embedding c) = Ioo (c + a) (c + b) :=
by { rw [← coe_inj, coe_map, coe_Ioo, coe_Ioo], exact set.image_const_add_Ioo _ _ _ }

@[simp] lemma map_add_right_Ioo (a b c : α) :
  (Ioo a b).map (add_right_embedding c) = Ioo (a + c) (b + c) :=
by { rw [← coe_inj, coe_map, coe_Ioo, coe_Ioo], exact set.image_add_const_Ioo _ _ _ }

variables [decidable_eq α]

@[simp] lemma image_add_left_Icc (a b c : α) : (Icc a b).image ((+) c) = Icc (c + a) (c + b) :=
by { rw [← map_add_left_Icc, map_eq_image], refl }

@[simp] lemma image_add_left_Ico (a b c : α) : (Ico a b).image ((+) c) = Ico (c + a) (c + b) :=
by { rw [← map_add_left_Ico, map_eq_image], refl }

@[simp] lemma image_add_left_Ioc (a b c : α) : (Ioc a b).image ((+) c) = Ioc (c + a) (c + b) :=
by { rw [← map_add_left_Ioc, map_eq_image], refl }

@[simp] lemma image_add_left_Ioo (a b c : α) : (Ioo a b).image ((+) c) = Ioo (c + a) (c + b) :=
by { rw [← map_add_left_Ioo, map_eq_image], refl }

@[simp] lemma image_add_right_Icc (a b c : α) : (Icc a b).image (+ c) = Icc (a + c) (b + c) :=
by { rw [← map_add_right_Icc, map_eq_image], refl }

lemma image_add_right_Ico (a b c : α) : (Ico a b).image (+ c) = Ico (a + c) (b + c) :=
by { rw [← map_add_right_Ico, map_eq_image], refl }

lemma image_add_right_Ioc (a b c : α) : (Ioc a b).image (+ c) = Ioc (a + c) (b + c) :=
by { rw [← map_add_right_Ioc, map_eq_image], refl }

lemma image_add_right_Ioo (a b c : α) : (Ioo a b).image (+ c) = Ioo (a + c) (b + c) :=
by { rw [← map_add_right_Ioo, map_eq_image], refl }

end ordered_cancel_add_comm_monoid

@[to_additive] lemma prod_prod_Ioi_mul_eq_prod_prod_off_diag [fintype ι] [linear_order ι]
  [locally_finite_order_top ι] [locally_finite_order_bot ι] [comm_monoid α] (f : ι → ι → α) :
  ∏ i, ∏ j in Ioi i, f j i * f i j = ∏ i, ∏ j in {i}ᶜ, f j i :=
begin
  simp_rw [←Ioi_disj_union_Iio, prod_disj_union, prod_mul_distrib],
  congr' 1,
  rw [prod_sigma', prod_sigma'],
  refine prod_bij' (λ i hi, ⟨i.2, i.1⟩) _ _ (λ i hi, ⟨i.2, i.1⟩) _ _ _; simp,
end

end finset
