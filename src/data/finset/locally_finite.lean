/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yaël Dillies
-/
import order.locally_finite

/-!
# Intervals as finsets

This file provides basic results about all the `finset.Ixx`, which are defined in
`order.locally_finite`.

## TODO

This file was originally only about `finset.Ico a b` where `a b : ℕ`. No care has yet been taken to
generalize these lemmas properly and many lemmas about `Icc`, `Ioc`, `Ioo` are missing. In general,
what's to do is taking the lemmas in `data.x.intervals` and abstract away the concrete structure.
-/

namespace finset
variables {α : Type*}
section preorder
variables [preorder α] [locally_finite_order α] {a b : α}

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

alias Icc_eq_empty_iff ↔ _ finset.Icc_eq_empty
alias Ico_eq_empty_iff ↔ _ finset.Ico_eq_empty
alias Ioc_eq_empty_iff ↔ _ finset.Ioc_eq_empty

@[simp] lemma Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x hx, h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp] lemma Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅ :=
Icc_eq_empty h.not_le

@[simp] lemma Ico_eq_empty_of_le (h : b ≤ a) : Ico a b = ∅ :=
Ico_eq_empty h.not_lt

@[simp] lemma Ioc_eq_empty_of_le (h : b ≤ a) : Ioc a b = ∅ :=
Ioc_eq_empty h.not_lt

@[simp] lemma Ioo_eq_empty_of_le (h : b ≤ a) : Ioo a b = ∅ :=
Ioo_eq_empty h.not_lt

variables (a)

@[simp] lemma Ico_self : Ico a a = ∅ :=
by rw [←coe_eq_empty, coe_Ico, set.Ico_self]

@[simp] lemma Ioc_self : Ioc a a = ∅ :=
by rw [←coe_eq_empty, coe_Ioc, set.Ioc_self]

@[simp] lemma Ioo_self : Ioo a a = ∅ :=
by rw [←coe_eq_empty, coe_Ioo, set.Ioo_self]

@[simp] lemma right_not_mem_Ico {a b : α} : b ∉ Ico a b :=
by { rw [mem_Ico, not_and], exact λ _, lt_irrefl _ }

lemma Ico_filter_lt_of_le_left [decidable_rel ((<) : α → α → Prop)] {a b c : α} (hca : c ≤ a) :
  (Ico a b).filter (λ x, x < c) = ∅ :=
finset.filter_false_of_mem (λ x hx, (hca.trans (mem_Ico.1 hx).1).not_lt)

lemma Ico_filter_lt_of_right_le [decidable_rel ((<) : α → α → Prop)] {a b c : α} (hbc : b ≤ c) :
  (Ico a b).filter (λ x, x < c) = Ico a b :=
finset.filter_true_of_mem (λ x hx, (mem_Ico.1 hx).2.trans_le hbc)

lemma Ico_filter_lt_of_le_right [decidable_rel ((<) : α → α → Prop)] {a b c : α} (hcb : c ≤ b) :
  (Ico a b).filter (λ x, x < c) = Ico a c :=
begin
  ext x,
  rw [mem_filter, mem_Ico, mem_Ico, and.right_comm],
  exact and_iff_left_of_imp (λ h, h.2.trans_le hcb),
end

lemma Ico_filter_le_of_le_left [decidable_rel ((≤) : α → α → Prop)] {a b c : α} (hca : c ≤ a) :
  (Ico a b).filter (λ x, c ≤ x) = Ico a b :=
finset.filter_true_of_mem (λ x hx, hca.trans (mem_Ico.1 hx).1)

lemma Ico_filter_le_of_right_le [decidable_rel ((≤) : α → α → Prop)] {a b : α} :
  (Ico a b).filter (λ x, b ≤ x) = ∅ :=
finset.filter_false_of_mem (λ x hx, (mem_Ico.1 hx).2.not_le)

lemma Ico_filter_le_of_left_le [decidable_rel ((≤) : α → α → Prop)] {a b c : α} (hac : a ≤ c) :
  (Ico a b).filter (λ x, c ≤ x) = Ico c b :=
begin
  ext x,
  rw [mem_filter, mem_Ico, mem_Ico, and_comm, and.left_comm],
  exact and_iff_right_of_imp (λ h, hac.trans h.1),
end

/-- A set with upper and lower bounds in a locally finite order is a fintype -/
def _root_.set.fintype_of_mem_bounds {a b} {s : set α} [decidable_pred (∈ s)]
  (ha : a ∈ lower_bounds s) (hb : b ∈ upper_bounds s) : fintype s :=
set.fintype_subset (set.Icc a b) $ λ x hx, ⟨ha hx, hb hx⟩

lemma _root_.bdd_below.finite_of_bdd_above {s : set α} (h₀ : bdd_below s) (h₁ : bdd_above s) :
  s.finite :=
let ⟨a, ha⟩ := h₀, ⟨b, hb⟩ := h₁ in by { classical, exact ⟨set.fintype_of_mem_bounds ha hb⟩ }

end preorder

section partial_order
variables [partial_order α] [locally_finite_order α] {a b : α}

@[simp] lemma Icc_self (a : α) : Icc a a = {a} :=
by rw [←coe_eq_singleton, coe_Icc, set.Icc_self]

lemma Ico_insert_right [decidable_eq α] (h : a ≤ b) : insert b (Ico a b) = Icc a b :=
by rw [←coe_inj, coe_insert, coe_Icc, coe_Ico, set.insert_eq, set.union_comm, set.Ico_union_right h]

lemma Ioo_insert_left [decidable_eq α] (h : a < b) : insert a (Ioo a b) = Ico a b :=
by rw [←coe_inj, coe_insert, coe_Ioo, coe_Ico, set.insert_eq, set.union_comm, set.Ioo_union_left h]

@[simp] lemma Ico_inter_Ico_consecutive [decidable_eq α] (a b c : α) : Ico a b ∩ Ico b c = ∅ :=
begin
  refine eq_empty_of_forall_not_mem (λ x hx, _),
  rw [mem_inter, mem_Ico, mem_Ico] at hx,
  exact hx.1.2.not_le hx.2.1,
end

lemma Ico_disjoint_Ico_consecutive [decidable_eq α] (a b c : α) : disjoint (Ico a b) (Ico b c) :=
le_of_eq $ Ico_inter_Ico_consecutive a b c

lemma Ico_filter_le_left [decidable_rel ((≤) : α → α → Prop)] {a b : α} (hab : a < b) :
  (Ico a b).filter (λ x, x ≤ a) = {a} :=
begin
  ext x,
  rw [mem_filter, mem_Ico, mem_singleton, and.right_comm, ←le_antisymm_iff, eq_comm],
  exact and_iff_left_of_imp (λ h, h.le.trans_lt hab),
end

end partial_order

section linear_order
variables [linear_order α] [locally_finite_order α] {a b : α}

lemma Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) :
  Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
by rw [←coe_subset, coe_Ico, coe_Ico, set.Ico_subset_Ico_iff h]

lemma Ico_union_Ico_eq_Ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
  Ico a b ∪ Ico b c = Ico a c :=
by rw [←coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, set.Ico_union_Ico_eq_Ico hab hbc]

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

end linear_order

section order_top
variables [order_top α] [locally_finite_order α]

lemma _root_.bdd_below.finite {s : set α} (hs : bdd_below s) : s.finite :=
hs.finite_of_bdd_above $ order_top.bdd_above s

end order_top

section order_bot
variables [order_bot α] [locally_finite_order α]

lemma _root_.bdd_above.finite {s : set α} (hs : bdd_above s) : s.finite := hs.dual.finite

end order_bot

section ordered_cancel_add_comm_monoid
variables [ordered_cancel_add_comm_monoid α] [has_exists_add_of_le α] [decidable_eq α]
  [locally_finite_order α]

lemma image_add_left_Icc (a b c : α) : (Icc a b).image ((+) c) = Icc (c + a) (c + b) :=
begin
  ext x,
  rw [mem_image, mem_Icc],
  split,
  { rintro ⟨y, hy, rfl⟩,
    rw mem_Icc at hy,
    exact ⟨add_le_add_left hy.1 c, add_le_add_left hy.2 c⟩ },
  { intro hx,
    obtain ⟨y, hy⟩ := exists_add_of_le hx.1,
    rw add_assoc at hy,
    rw hy at hx,
    exact ⟨a + y, mem_Icc.2 ⟨le_of_add_le_add_left hx.1, le_of_add_le_add_left hx.2⟩, hy.symm⟩ }
end

lemma image_add_left_Ico (a b c : α) : (Ico a b).image ((+) c) = Ico (c + a) (c + b) :=
begin
  ext x,
  rw [mem_image, mem_Ico],
  split,
  { rintro ⟨y, hy, rfl⟩,
    rw mem_Ico at hy,
    exact ⟨add_le_add_left hy.1 c, add_lt_add_left hy.2 c⟩ },
  { intro hx,
    obtain ⟨y, hy⟩ := exists_add_of_le hx.1,
    rw add_assoc at hy,
    rw hy at hx,
    exact ⟨a + y, mem_Ico.2 ⟨le_of_add_le_add_left hx.1, lt_of_add_lt_add_left hx.2⟩, hy.symm⟩ }
end

lemma image_add_left_Ioc (a b c : α) : (Ioc a b).image ((+) c) = Ioc (c + a) (c + b) :=
begin
  ext x,
  rw [mem_image, mem_Ioc],
  refine ⟨_, λ hx, _⟩,
  { rintro ⟨y, hy, rfl⟩,
    rw mem_Ioc at hy,
    exact ⟨add_lt_add_left hy.1 c, add_le_add_left hy.2 c⟩ },
  { obtain ⟨y, hy⟩ := exists_add_of_le hx.1.le,
    rw add_assoc at hy,
    rw hy at hx,
    exact ⟨a + y, mem_Ioc.2 ⟨lt_of_add_lt_add_left hx.1, le_of_add_le_add_left hx.2⟩, hy.symm⟩ }
end

lemma image_add_left_Ioo (a b c : α) : (Ioo a b).image ((+) c) = Ioo (c + a) (c + b) :=
begin
  ext x,
  rw [mem_image, mem_Ioo],
  refine ⟨_, λ hx, _⟩,
  { rintro ⟨y, hy, rfl⟩,
    rw mem_Ioo at hy,
    exact ⟨add_lt_add_left hy.1 c, add_lt_add_left hy.2 c⟩ },
  { obtain ⟨y, hy⟩ := exists_add_of_le hx.1.le,
    rw add_assoc at hy,
    rw hy at hx,
    exact ⟨a + y, mem_Ioo.2 ⟨lt_of_add_lt_add_left hx.1, lt_of_add_lt_add_left hx.2⟩, hy.symm⟩ }
end

lemma image_add_right_Icc (a b c : α) : (Icc a b).image (λ x, x + c) = Icc (a + c) (b + c) :=
by { simp_rw add_comm _ c, exact image_add_left_Icc a b c }

lemma image_add_right_Ico (a b c : α) : (Ico a b).image (λ x, x + c) = Ico (a + c) (b + c) :=
by { simp_rw add_comm _ c, exact image_add_left_Ico a b c }

lemma image_add_right_Ioc (a b c : α) : (Ioc a b).image (λ x, x + c) = Ioc (a + c) (b + c) :=
by { simp_rw add_comm _ c, exact image_add_left_Ioc a b c }

lemma image_add_right_Ioo (a b c : α) : (Ioo a b).image (λ x, x + c) = Ioo (a + c) (b + c) :=
by { simp_rw add_comm _ c, exact image_add_left_Ioo a b c }

end ordered_cancel_add_comm_monoid
end finset
