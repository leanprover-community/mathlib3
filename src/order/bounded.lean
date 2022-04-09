/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import order.min_max
import order.rel_classes
import data.set.intervals.basic

/-!
# Bounded and unbounded sets

We prove miscellaneous lemmas about bounded and unbounded sets. Many of these are just variations on
the same ideas, or similar results with a few minor differences. The file is divided into these
different general ideas.
-/

namespace set
variables {α : Type*} {r : α → α → Prop} {s t : set α}

/-! ### Subsets of bounded and unbounded sets -/

theorem bounded.mono (hst : s ⊆ t) (hs : bounded r t) : bounded r s :=
hs.imp $ λ a ha b hb, ha b (hst hb)

theorem unbounded.mono (hst : s ⊆ t) (hs : unbounded r s) : unbounded r t :=
λ a, let ⟨b, hb, hb'⟩ := hs a in ⟨b, hst hb, hb'⟩

/-! ### Alternate characterizations of unboundedness on orders -/

lemma unbounded_le_of_forall_exists_lt [preorder α] (h : ∀ a, ∃ b ∈ s, a < b) : unbounded (≤) s :=
λ a, let ⟨b, hb, hb'⟩ := h a in ⟨b, hb, λ hba, hba.not_lt hb'⟩

lemma unbounded_le_iff [linear_order α] : unbounded (≤) s ↔ ∀ a, ∃ b ∈ s, a < b :=
by simp only [unbounded, not_le]

lemma unbounded_lt_of_forall_exists_le [preorder α] (h : ∀ a, ∃ b ∈ s, a ≤ b) : unbounded (<) s :=
λ a, let ⟨b, hb, hb'⟩ := h a in ⟨b, hb, λ hba, hba.not_le hb'⟩

lemma unbounded_lt_iff [linear_order α] : unbounded (<) s ↔ ∀ a, ∃ b ∈ s, a ≤ b :=
by simp only [unbounded, not_lt]

lemma unbounded_ge_of_forall_exists_gt [preorder α] (h : ∀ a, ∃ b ∈ s, b < a) : unbounded (≥) s :=
@unbounded_le_of_forall_exists_lt (order_dual α) _ _ h

lemma unbounded_ge_iff [linear_order α] : unbounded (≥) s ↔ ∀ a, ∃ b ∈ s, b < a :=
⟨λ h a, let ⟨b, hb, hba⟩ := h a in ⟨b, hb, lt_of_not_ge hba⟩, unbounded_ge_of_forall_exists_gt⟩

lemma unbounded_gt_of_forall_exists_ge [preorder α] (h : ∀ a, ∃ b ∈ s, b ≤ a) : unbounded (>) s :=
λ a, let ⟨b, hb, hb'⟩ := h a in ⟨b, hb, λ hba, not_le_of_gt hba hb'⟩

lemma unbounded_gt_iff [linear_order α] : unbounded (>) s ↔ ∀ a, ∃ b ∈ s, b ≤ a :=
⟨λ h a, let ⟨b, hb, hba⟩ := h a in ⟨b, hb, le_of_not_gt hba⟩, unbounded_gt_of_forall_exists_ge⟩

/-! ### Relation between boundedness by strict and nonstrict orders. -/

/-! #### Less and less or equal -/

lemma bounded.rel_mono {r' : α → α → Prop} (h : bounded r s) (hrr' : r ≤ r') : bounded r' s :=
let ⟨a, ha⟩ := h in ⟨a, λ b hb, hrr' b a (ha b hb)⟩

lemma bounded_le_of_bounded_lt [preorder α] (h : bounded (<) s) : bounded (≤) s :=
h.rel_mono $ λ _ _, le_of_lt

lemma unbounded.rel_mono {r' : α → α → Prop} (hr : r' ≤ r) (h : unbounded r s) : unbounded r' s :=
λ a, let ⟨b, hb, hba⟩ := h a in ⟨b, hb, λ hba', hba (hr b a hba')⟩

lemma unbounded_lt_of_unbounded_le [preorder α] (h : unbounded (≤) s) :
  unbounded (<) s :=
h.rel_mono $ λ _ _, le_of_lt

lemma bounded_le_iff_bounded_lt [preorder α] [no_max_order α] : bounded (≤) s ↔ bounded (<) s :=
begin
  refine ⟨λ h, _, bounded_le_of_bounded_lt⟩,
  cases h with a ha,
  cases exists_gt a with b hb,
  exact ⟨b, λ c hc, lt_of_le_of_lt (ha c hc) hb⟩
end

lemma unbounded_lt_iff_unbounded_le [preorder α] [no_max_order α] :
  unbounded (<) s ↔ unbounded (≤) s :=
by simp_rw [← not_bounded_iff, bounded_le_iff_bounded_lt]

/-! #### Greater and greater or equal -/

lemma bounded_ge_of_bounded_gt [preorder α] (h : bounded (>) s) : bounded (≥) s :=
let ⟨a, ha⟩ := h in ⟨a, λ b hb, le_of_lt (ha b hb)⟩

lemma unbounded_gt_of_unbounded_ge [preorder α] (h : unbounded (≥) s) : unbounded (>) s :=
λ a, let ⟨b, hb, hba⟩ := h a in ⟨b, hb, λ hba', hba (le_of_lt hba')⟩

lemma bounded_ge_iff_bounded_gt [preorder α] [no_min_order α] : bounded (≥) s ↔ bounded (>) s :=
@bounded_le_iff_bounded_lt (order_dual α) _ _ _

lemma unbounded_gt_iff_unbounded_ge [preorder α] [no_min_order α] :
  unbounded (>) s ↔ unbounded (≥) s :=
@unbounded_lt_iff_unbounded_le (order_dual α) _ _ _

/-! ### The universal set -/

theorem unbounded_le_univ [has_le α] [no_top_order α] : unbounded (≤) (@set.univ α) :=
λ a, let ⟨b, hb⟩ := exists_not_le a in ⟨b, ⟨⟩, hb⟩

theorem unbounded_lt_univ [preorder α] [no_top_order α] : unbounded (<) (@set.univ α) :=
unbounded_lt_of_unbounded_le unbounded_le_univ

theorem unbounded_ge_univ [has_le α] [no_bot_order α] : unbounded (≥) (@set.univ α) :=
λ a, let ⟨b, hb⟩ := exists_not_ge a in ⟨b, ⟨⟩, hb⟩

theorem unbounded_gt_univ [preorder α] [no_bot_order α] : unbounded (>) (@set.univ α) :=
unbounded_gt_of_unbounded_ge unbounded_ge_univ

/-! ### Bounded and unbounded intervals -/

theorem bounded_self (a : α) : bounded r {b | r b a} :=
⟨a, λ x, id⟩

/-! #### Half-open bounded intervals -/

theorem bounded_lt_Iio [preorder α] (a : α) : bounded (<) (set.Iio a) :=
bounded_self a

theorem bounded_le_Iio [preorder α] (a : α) : bounded (≤) (set.Iio a) :=
bounded_le_of_bounded_lt (bounded_lt_Iio a)

theorem bounded_le_Iic [preorder α] (a : α) : bounded (≤) (set.Iic a) :=
bounded_self a

theorem bounded_lt_Iic [preorder α] [no_max_order α] (a : α) : bounded (<) (set.Iic a) :=
by simp only [← bounded_le_iff_bounded_lt, bounded_le_Iic]

theorem bounded_gt_Ioi [preorder α] (a : α) : bounded (>) (set.Ioi a) :=
bounded_self a

theorem bounded_ge_Ioi [preorder α] (a : α) : bounded (≥) (set.Ioi a) :=
bounded_ge_of_bounded_gt (bounded_gt_Ioi a)

theorem bounded_ge_Ici [preorder α] (a : α) : bounded (≥) (set.Ici a) :=
bounded_self a

theorem bounded_gt_Ici [preorder α] [no_min_order α] (a : α) : bounded (>) (set.Ici a) :=
by simp only [← bounded_ge_iff_bounded_gt, bounded_ge_Ici]

/-! #### Other bounded intervals -/

theorem bounded_lt_Ioo [preorder α] (a b : α) : bounded (<) (set.Ioo a b) :=
(bounded_lt_Iio b).mono set.Ioo_subset_Iio_self

theorem bounded_lt_Ico [preorder α] (a b : α) : bounded (<) (set.Ico a b) :=
(bounded_lt_Iio b).mono set.Ico_subset_Iio_self

theorem bounded_lt_Ioc [preorder α] [no_max_order α] (a b : α) : bounded (<) (set.Ioc a b) :=
(bounded_lt_Iic b).mono set.Ioc_subset_Iic_self

theorem bounded_lt_Icc [preorder α] [no_max_order α] (a b : α) : bounded (<) (set.Icc a b) :=
(bounded_lt_Iic b).mono set.Icc_subset_Iic_self

theorem bounded_le_Ioo [preorder α] (a b : α) : bounded (≤) (set.Ioo a b) :=
(bounded_le_Iio b).mono set.Ioo_subset_Iio_self

theorem bounded_le_Ico [preorder α] (a b : α) : bounded (≤) (set.Ico a b) :=
(bounded_le_Iio b).mono set.Ico_subset_Iio_self

theorem bounded_le_Ioc [preorder α] (a b : α) : bounded (≤) (set.Ioc a b) :=
(bounded_le_Iic b).mono set.Ioc_subset_Iic_self

theorem bounded_le_Icc [preorder α] (a b : α) : bounded (≤) (set.Icc a b) :=
(bounded_le_Iic b).mono set.Icc_subset_Iic_self

theorem bounded_gt_Ioo [preorder α] (a b : α) : bounded (>) (set.Ioo a b) :=
(bounded_gt_Ioi a).mono set.Ioo_subset_Ioi_self

theorem bounded_gt_Ioc [preorder α] (a b : α) : bounded (>) (set.Ioc a b) :=
(bounded_gt_Ioi a).mono set.Ioc_subset_Ioi_self

theorem bounded_gt_Ico [preorder α] [no_min_order α] (a b : α) : bounded (>) (set.Ico a b) :=
(bounded_gt_Ici a).mono set.Ico_subset_Ici_self

theorem bounded_gt_Icc [preorder α] [no_min_order α] (a b : α) : bounded (>) (set.Icc a b) :=
(bounded_gt_Ici a).mono set.Icc_subset_Ici_self

theorem bounded_ge_Ioo [preorder α] (a b : α) : bounded (≥) (set.Ioo a b) :=
(bounded_ge_Ioi a).mono set.Ioo_subset_Ioi_self

theorem bounded_ge_Ioc [preorder α] (a b : α) : bounded (≥) (set.Ioc a b) :=
(bounded_ge_Ioi a).mono set.Ioc_subset_Ioi_self

theorem bounded_ge_Ico [preorder α] (a b : α) : bounded (≥) (set.Ico a b) :=
(bounded_ge_Ici a).mono set.Ico_subset_Ici_self

theorem bounded_ge_Icc [preorder α] (a b : α) : bounded (≥) (set.Icc a b) :=
(bounded_ge_Ici a).mono set.Icc_subset_Ici_self

/-! #### Unbounded intervals -/

theorem unbounded_le_Ioi [semilattice_sup α] [no_max_order α] (a : α) : unbounded (≤) (set.Ioi a) :=
λ b, let ⟨c, hc⟩ := exists_gt (a ⊔ b) in
  ⟨c, le_sup_left.trans_lt hc, (le_sup_right.trans_lt hc).not_le⟩

theorem unbounded_le_Ici [semilattice_sup α] [no_max_order α] (a : α) : unbounded (≤) (set.Ici a) :=
(unbounded_le_Ioi a).mono set.Ioi_subset_Ici_self

theorem unbounded_lt_Ioi [semilattice_sup α] [no_max_order α] (a : α) : unbounded (<) (set.Ioi a) :=
unbounded_lt_of_unbounded_le (unbounded_le_Ioi a)

theorem unbounded_lt_Ici [semilattice_sup α] (a : α) : unbounded (<) (set.Ici a) :=
λ b, ⟨a ⊔ b, le_sup_left, le_sup_right.not_lt⟩

/-! ### Bounded initial segments -/

theorem bounded_inter_not (H : ∀ a b, ∃ m, ∀ c, r c a ∨ r c b → r c m) (a : α) :
  bounded r (s ∩ {b | ¬ r b a}) ↔ bounded r s :=
begin
  refine ⟨_, bounded.mono (set.inter_subset_left s _)⟩,
  rintro ⟨b, hb⟩,
  cases H a b with m hm,
  exact ⟨m, λ c hc, hm c (or_iff_not_imp_left.2 (λ hca, (hb c ⟨hc, hca⟩)))⟩
end

theorem unbounded_inter_not (H : ∀ a b, ∃ m, ∀ c, r c a ∨ r c b → r c m) (a : α) :
  unbounded r (s ∩ {b | ¬ r b a}) ↔ unbounded r s :=
by simp_rw [← not_bounded_iff, bounded_inter_not H]

/-! #### Less or equal -/

theorem bounded_le_inter_not_le [semilattice_sup α] (a : α) :
  bounded (≤) (s ∩ {b | ¬ b ≤ a}) ↔ bounded (≤) s :=
bounded_inter_not (λ x y, ⟨x ⊔ y, λ z h, h.elim le_sup_of_le_left le_sup_of_le_right⟩) a

theorem unbounded_le_inter_not_le [semilattice_sup α] (a : α) :
  unbounded (≤) (s ∩ {b | ¬ b ≤ a}) ↔ unbounded (≤) s :=
begin
  rw [←not_bounded_iff, ←not_bounded_iff, not_iff_not],
  exact bounded_le_inter_not_le a
end

theorem bounded_le_inter_lt [linear_order α] (a : α) :
  bounded (≤) (s ∩ {b | a < b}) ↔ bounded (≤) s :=
by simp_rw [← not_le, bounded_le_inter_not_le]

theorem unbounded_le_inter_lt [linear_order α] (a : α) :
  unbounded (≤) (s ∩ {b | a < b}) ↔ unbounded (≤) s :=
by { convert unbounded_le_inter_not_le a, ext, exact lt_iff_not_ge' }

theorem bounded_le_inter_le [linear_order α] (a : α) :
  bounded (≤) (s ∩ {b | a ≤ b}) ↔ bounded (≤) s :=
begin
  refine ⟨_, bounded.mono (set.inter_subset_left s _)⟩,
  rw ←@bounded_le_inter_lt _ s _ a,
  exact bounded.mono (λ x ⟨hx, hx'⟩, ⟨hx, le_of_lt hx'⟩)
end

theorem unbounded_le_inter_le [linear_order α] (a : α) :
  unbounded (≤) (s ∩ {b | a ≤ b}) ↔ unbounded (≤) s :=
begin
  rw [←not_bounded_iff, ←not_bounded_iff, not_iff_not],
  exact bounded_le_inter_le a
end

/-! #### Less than -/

theorem bounded_lt_inter_not_lt [semilattice_sup α] (a : α) :
  bounded (<) (s ∩ {b | ¬ b < a}) ↔ bounded (<) s :=
bounded_inter_not (λ x y, ⟨x ⊔ y, λ z h, h.elim lt_sup_of_lt_left lt_sup_of_lt_right⟩) a

theorem unbounded_lt_inter_not_lt [semilattice_sup α] (a : α) :
  unbounded (<) (s ∩ {b | ¬ b < a}) ↔ unbounded (<) s :=
begin
  rw [←not_bounded_iff, ←not_bounded_iff, not_iff_not],
  exact bounded_lt_inter_not_lt a
end

theorem bounded_lt_inter_le [linear_order α] (a : α) :
  bounded (<) (s ∩ {b | a ≤ b}) ↔ bounded (<) s :=
by { convert bounded_lt_inter_not_lt a, ext, exact not_lt.symm }

theorem unbounded_lt_inter_le [linear_order α] (a : α) :
  unbounded (<) (s ∩ {b | a ≤ b}) ↔ unbounded (<) s :=
by { convert unbounded_lt_inter_not_lt a, ext, exact not_lt.symm }

theorem bounded_lt_inter_lt [linear_order α] [no_max_order α] (a : α) :
  bounded (<) (s ∩ {b | a < b}) ↔ bounded (<) s :=
begin
  rw [←bounded_le_iff_bounded_lt, ←bounded_le_iff_bounded_lt],
  exact bounded_le_inter_lt a
end

theorem unbounded_lt_inter_lt [linear_order α] [no_max_order α] (a : α) :
  unbounded (<) (s ∩ {b | a < b}) ↔ unbounded (<) s :=
begin
  rw [←not_bounded_iff, ←not_bounded_iff, not_iff_not],
  exact bounded_lt_inter_lt a
end

/-! #### Greater or equal -/

theorem bounded_ge_inter_not_ge [semilattice_inf α] (a : α) :
  bounded (≥) (s ∩ {b | ¬ a ≤ b}) ↔ bounded (≥) s :=
@bounded_le_inter_not_le (order_dual α) s _ a

theorem unbounded_ge_inter_not_ge [semilattice_inf α] (a : α) :
  unbounded (≥) (s ∩ {b | ¬ a ≤ b}) ↔ unbounded (≥) s :=
@unbounded_le_inter_not_le (order_dual α) s _ a

theorem bounded_ge_inter_gt [linear_order α] (a : α) :
  bounded (≥) (s ∩ {b | b < a}) ↔ bounded (≥) s :=
@bounded_le_inter_lt (order_dual α) s _ a

theorem unbounded_ge_inter_gt [linear_order α] (a : α) :
  unbounded (≥) (s ∩ {b | b < a}) ↔ unbounded (≥) s :=
@unbounded_le_inter_lt (order_dual α) s _ a

theorem bounded_ge_inter_ge [linear_order α] (a : α) :
  bounded (≥) (s ∩ {b | b ≤ a}) ↔ bounded (≥) s :=
@bounded_le_inter_le (order_dual α) s _ a

theorem unbounded_ge_iff_unbounded_inter_ge [linear_order α] (a : α) :
  unbounded (≥) (s ∩ {b | b ≤ a}) ↔ unbounded (≥) s :=
@unbounded_le_inter_le (order_dual α) s _ a

/-! #### Greater than -/

theorem bounded_gt_inter_not_gt [semilattice_inf α] (a : α) :
  bounded (>) (s ∩ {b | ¬ a < b}) ↔ bounded (>) s :=
@bounded_lt_inter_not_lt (order_dual α) s _ a

theorem unbounded_gt_inter_not_gt [semilattice_inf α] (a : α) :
  unbounded (>) (s ∩ {b | ¬ a < b}) ↔ unbounded (>) s :=
@unbounded_lt_inter_not_lt (order_dual α) s _ a

theorem bounded_gt_inter_ge [linear_order α] (a : α) :
  bounded (>) (s ∩ {b | b ≤ a}) ↔ bounded (>) s :=
@bounded_lt_inter_le (order_dual α) s _ a

theorem unbounded_inter_ge [linear_order α] (a : α) :
  unbounded (>) (s ∩ {b | b ≤ a}) ↔ unbounded (>) s :=
@unbounded_lt_inter_le (order_dual α) s _ a

theorem bounded_gt_inter_gt [linear_order α] [no_min_order α] (a : α) :
  bounded (>) (s ∩ {b | b < a}) ↔ bounded (>) s :=
@bounded_lt_inter_lt (order_dual α) s _ _ a

theorem unbounded_gt_inter_gt [linear_order α] [no_min_order α] (a : α) :
  unbounded (>) (s ∩ {b | b < a}) ↔ unbounded (>) s :=
@unbounded_lt_inter_lt (order_dual α) s _ _ a

end set
