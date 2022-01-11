/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import .min_max
import .rel_classes
import data.set.intervals.basic

/-!
# Bounded and unbounded sets

We prove miscellaneous lemmas about bounded and unbounded sets. Many of these are just variations on
the same ideas, or similar results with a few minor differences. The file is divided into these
different general ideas.
-/

variables {α : Type*} {r : α → α → Prop} {s t : set α}

/-! ### Subsets of bounded and unbounded sets -/

theorem bounded_of_subset_bounded (hst : s ⊆ t) (hs : bounded r t) : bounded r s :=
hs.imp $ λ a ha b hb, ha b (hst hb)

theorem unbounded_of_unbounded_subset (hst : s ⊆ t) (hs : unbounded r s) : unbounded r t :=
λ a, let ⟨b, hb, hb'⟩ := hs a in ⟨b, hst hb, hb'⟩

/-! ### Alternate characterizations of unboundedness on orders -/

lemma unbounded_le_of_forall_ex_lt [preorder α] (h : ∀ a, ∃ b ∈ s, a < b) : unbounded (≤) s :=
λ a, let ⟨b, hb, hb'⟩ := h a in ⟨b, hb, λ hba, not_lt_of_ge hba hb'⟩

lemma unbounded_le_iff [linear_order α] : unbounded (≤) s ↔ ∀ a, ∃ b ∈ s, a < b :=
⟨λ h a, let ⟨b, hb, hba⟩ := h a in ⟨b, hb, lt_of_not_ge hba⟩, unbounded_le_of_forall_ex_lt⟩

lemma unbounded_lt_of_forall_ex_le [preorder α] (h : ∀ a, ∃ b ∈ s, a ≤ b) : unbounded (<) s :=
λ a, let ⟨b, hb, hb'⟩ := h a in ⟨b, hb, λ hba, not_le_of_gt hba hb'⟩

lemma unbounded_lt_iff [linear_order α] : unbounded (<) s ↔ ∀ a, ∃ b ∈ s, a ≤ b :=
⟨λ h a, let ⟨b, hb, hba⟩ := h a in ⟨b, hb, le_of_not_gt hba⟩, unbounded_lt_of_forall_ex_le⟩

lemma unbounded_ge_of_forall_ex_gt [preorder α] (h : ∀ a, ∃ b ∈ s, b < a) : unbounded (≥) s :=
λ a, let ⟨b, hb, hb'⟩ := h a in ⟨b, hb, λ hba, not_lt_of_ge hba hb'⟩

lemma unbounded_ge_iff [linear_order α] : unbounded (≥) s ↔ ∀ a, ∃ b ∈ s, b < a :=
⟨λ h a, let ⟨b, hb, hba⟩ := h a in ⟨b, hb, lt_of_not_ge hba⟩, unbounded_ge_of_forall_ex_gt⟩

lemma unbounded_gt_of_forall_ex_ge [preorder α] (h : ∀ a, ∃ b ∈ s, b ≤ a) : unbounded (>) s :=
λ a, let ⟨b, hb, hb'⟩ := h a in ⟨b, hb, λ hba, not_le_of_gt hba hb'⟩

lemma unbounded_gt_iff [linear_order α] : unbounded (>) s ↔ ∀ a, ∃ b ∈ s, b ≤ a :=
⟨λ h a, let ⟨b, hb, hba⟩ := h a in ⟨b, hb, le_of_not_gt hba⟩, unbounded_gt_of_forall_ex_ge⟩

/-! ### Relation between boundedness by strict and nonstrict orders. -/

/-! #### Less and less or equal -/

lemma bounded_le_of_bounded_lt [preorder α] (h : bounded (<) s) : bounded (≤) s :=
let ⟨a, ha⟩ := h in ⟨a, λ b hb, le_of_lt (ha b hb)⟩

lemma unbounded_lt_of_unbounded_le [preorder α] (h : unbounded (≤) s) :
  unbounded (<) s :=
λ a, let ⟨b, hb, hba⟩ := h a in ⟨b, hb, λ hba', hba (le_of_lt hba')⟩

lemma bounded_le_iff_bounded_lt [preorder α] [no_top_order α] : bounded (≤) s ↔ bounded (<) s :=
begin
  refine ⟨λ h, _, bounded_le_of_bounded_lt⟩,
  cases h with a ha,
  cases no_top a with b hb,
  exact ⟨b, λ c hc, lt_of_le_of_lt (ha c hc) hb⟩
end

lemma unbounded_lt_iff_unbounded_le [preorder α] [no_top_order α] :
  unbounded (<) s ↔ unbounded (≤) s :=
begin
  refine ⟨λ h a, _, unbounded_lt_of_unbounded_le⟩,
  cases no_top a with c hc,
  rcases h c with ⟨b, hb, hbc⟩,
  exact ⟨b, hb, λ hba, hbc (lt_of_le_of_lt hba hc)⟩
end

/-! #### Greater and greater or equal -/

lemma bounded_ge_of_bounded_gt [preorder α] (h : bounded (>) s) : bounded (≥) s :=
let ⟨a, ha⟩ := h in ⟨a, λ b hb, le_of_lt (ha b hb)⟩

lemma unbounded_gt_of_unbounded_ge [preorder α] (h : unbounded (≥) s) : unbounded (>) s :=
λ a, let ⟨b, hb, hba⟩ := h a in ⟨b, hb, λ hba', hba (le_of_lt hba')⟩

lemma bounded_ge_iff_bounded_gt [preorder α] [no_bot_order α] : bounded (≥) s ↔ bounded (>) s :=
begin
  refine ⟨λ h, _, bounded_ge_of_bounded_gt⟩,
  cases h with a ha,
  cases no_bot a with b hb,
  exact ⟨b, λ c hc, lt_of_lt_of_le hb (ha c hc)⟩
end

lemma unbounded_ge_iff_unbounded_gt [preorder α] [no_bot_order α] :
  unbounded (≥) s ↔ unbounded (>) s :=
begin
  refine ⟨unbounded_gt_of_unbounded_ge, λ h a, _⟩,
  cases no_bot a with c hc,
  rcases h c with ⟨b, hb, hbc⟩,
  exact ⟨b, hb, λ hba, hbc (lt_of_lt_of_le hc hba)⟩
end

/-! ### Bounded and unbounded intervals -/

theorem bounded_r_r (a : α) : bounded r {b | r b a} :=
⟨a, λ x, id⟩

/-! #### Half-open bounded intervals -/

theorem bounded_lt_Iio [preorder α] (a : α) : bounded (<) (set.Iio a) :=
bounded_r_r a

theorem bounded_lt_Iic [preorder α] [no_top_order α] (a : α) : bounded (<) (set.Iic a) :=
let ⟨b, hab⟩ := no_top a in ⟨b, λ c hca, lt_of_le_of_lt hca hab⟩

theorem bounded_le_Iio [preorder α] (a : α) : bounded (≤) (set.Iio a) :=
bounded_le_of_bounded_lt (bounded_lt_Iio a)

theorem bounded_le_Iic [preorder α] (a : α) : bounded (≤) (set.Iic a) :=
bounded_r_r a

theorem bounded_gt_Ioi [preorder α] (a : α) : bounded (>) (set.Ioi a) :=
bounded_r_r a

theorem bounded_gt_Ici [preorder α] [no_bot_order α] (a : α) : bounded (>) (set.Ici a) :=
exists.elim (no_bot a) $ λ b hab, ⟨b, λ c hca, lt_of_lt_of_le hab hca⟩

theorem bounded_ge_Ioi [preorder α] (a : α) : bounded (≥) (set.Ioi a) :=
bounded_ge_of_bounded_gt (bounded_gt_Ioi a)

theorem bounded_ge_Ici [preorder α] (a : α) : bounded (≥) (set.Ici a) :=
bounded_r_r a

/-! #### Other bounded intervals -/

theorem bounded_lt_Ioo [preorder α] (a b : α) : bounded (<) (set.Ioo a b) :=
bounded_of_subset_bounded set.Ioo_subset_Iio_self (bounded_lt_Iio b)

theorem bounded_lt_Ico [preorder α] (a b : α) : bounded (<) (set.Ico a b) :=
bounded_of_subset_bounded set.Ico_subset_Iio_self (bounded_lt_Iio b)

theorem bounded_lt_Ioc [preorder α] [no_top_order α] (a b : α) : bounded (<) (set.Ioc a b) :=
bounded_of_subset_bounded set.Ioc_subset_Iic_self (bounded_lt_Iic b)

theorem bounded_lt_Icc [preorder α] [no_top_order α] (a b : α) : bounded (<) (set.Icc a b) :=
bounded_of_subset_bounded set.Icc_subset_Iic_self (bounded_lt_Iic b)

theorem bounded_le_Ioo [preorder α] (a b : α) : bounded (≤) (set.Ioo a b) :=
bounded_of_subset_bounded set.Ioo_subset_Iio_self (bounded_le_Iio b)

theorem bounded_le_Ico [preorder α] (a b : α) : bounded (≤) (set.Ico a b) :=
bounded_of_subset_bounded set.Ico_subset_Iio_self (bounded_le_Iio b)

theorem bounded_le_Ioc [preorder α] (a b : α) : bounded (≤) (set.Ioc a b) :=
bounded_of_subset_bounded set.Ioc_subset_Iic_self (bounded_le_Iic b)

theorem bounded_le_Icc [preorder α] (a b : α) : bounded (≤) (set.Icc a b) :=
bounded_of_subset_bounded set.Icc_subset_Iic_self (bounded_le_Iic b)

theorem bounded_gt_Ioo [preorder α] (a b : α) : bounded (>) (set.Ioo a b) :=
bounded_of_subset_bounded set.Ioo_subset_Ioi_self (bounded_gt_Ioi a)

theorem bounded_gt_Ioc [preorder α] (a b : α) : bounded (>) (set.Ioc a b) :=
bounded_of_subset_bounded set.Ioc_subset_Ioi_self (bounded_gt_Ioi a)

theorem bounded_gt_Ico [preorder α] [no_bot_order α] (a b : α) : bounded (>) (set.Ico a b) :=
bounded_of_subset_bounded set.Ico_subset_Ici_self (bounded_gt_Ici a)

theorem bounded_gt_Icc [preorder α] [no_bot_order α] (a b : α) : bounded (>) (set.Icc a b) :=
bounded_of_subset_bounded set.Icc_subset_Ici_self (bounded_gt_Ici a)

theorem bounded_ge_Ioo [preorder α] (a b : α) : bounded (≥) (set.Ioo a b) :=
bounded_of_subset_bounded set.Ioo_subset_Ioi_self (bounded_ge_Ioi a)

theorem bounded_ge_Ioc [preorder α] (a b : α) : bounded (≥) (set.Ioc a b) :=
bounded_of_subset_bounded set.Ioc_subset_Ioi_self (bounded_ge_Ioi a)

theorem bounded_ge_Ico [preorder α] (a b : α) : bounded (≥) (set.Ico a b) :=
bounded_of_subset_bounded set.Ico_subset_Ici_self (bounded_ge_Ici a)

theorem bounded_ge_Icc [preorder α] (a b : α) : bounded (≥) (set.Icc a b) :=
bounded_of_subset_bounded set.Icc_subset_Ici_self (bounded_ge_Ici a)

/-! #### Unbounded intervals -/

theorem unbounded_le_Ioi [semilattice_sup α] [no_top_order α] (a : α) : unbounded (≤) (set.Ioi a) :=
λ b, let ⟨c, hc⟩ := no_top (a ⊔ b) in
  ⟨c, le_sup_left.trans_lt hc, not_le_of_gt (le_sup_right.trans_lt hc)⟩

theorem unbounded_le_Ici [semilattice_sup α] [no_top_order α] (a : α) : unbounded (≤) (set.Ici a) :=
unbounded_of_unbounded_subset set.Ioi_subset_Ici_self (unbounded_le_Ioi a)

theorem unbounded_lt_Ioi [semilattice_sup α] [no_top_order α] (a : α) : unbounded (<) (set.Ioi a) :=
unbounded_lt_of_unbounded_le (unbounded_le_Ioi a)

theorem unbounded_lt_Ici [semilattice_sup α] (a : α) : unbounded (<) (set.Ici a) :=
λ b, ⟨a ⊔ b, le_sup_left, not_lt_of_ge le_sup_right⟩

/-! ### Bounded initial segments -/

theorem bounded_r_iff_bounded_inter_not_r (H : ∀ a b, ∃ m, ∀ c, r c a ∨ r c b → r c m) (a : α) :
  bounded r s ↔ bounded r (s ∩ {b | ¬ r b a}) :=
begin
  use bounded_of_subset_bounded (set.inter_subset_left s _),
  rintro ⟨b, hb⟩,
  cases H a b with m hm,
  exact ⟨m, λ c hc, hm c (or_iff_not_imp_left.2 (λ hca, (hb c ⟨hc, hca⟩)))⟩
end

theorem unbounded_r_iff_unbounded_inter_not_r (H : ∀ a b, ∃ m, ∀ c, r c a ∨ r c b → r c m) (a : α) :
  unbounded r s ↔ unbounded r (s ∩ {b | ¬ r b a}) :=
begin
  rw [←not_bounded_iff, ←not_bounded_iff, not_iff_not],
  exact bounded_r_iff_bounded_inter_not_r H a
end

/-! #### Less or equal -/

theorem bounded_le_iff_bounded_inter_not_le [semilattice_sup α] (a : α) :
  bounded (≤) s ↔ bounded (≤) (s ∩ {b | ¬ b ≤ a}) :=
bounded_r_iff_bounded_inter_not_r
  (λ x y, ⟨x ⊔ y, λ z h, h.elim le_sup_of_le_left le_sup_of_le_right⟩) a

theorem unbounded_le_iff_unbounded_inter_not_le [semilattice_sup α] (a : α) :
  unbounded (≤) s ↔ unbounded (≤) (s ∩ {b | ¬ b ≤ a}) :=
begin
  rw [←not_bounded_iff, ←not_bounded_iff, not_iff_not],
  exact bounded_le_iff_bounded_inter_not_le a
end

theorem bounded_le_iff_bounded_inter_lt [linear_order α] (a : α) :
  bounded (≤) s ↔ bounded (≤) (s ∩ {b | a < b}) :=
by { convert bounded_le_iff_bounded_inter_not_le a, ext, exact lt_iff_not_ge' }

theorem unbounded_le_iff_unbounded_inter_lt [linear_order α] (a : α) :
  unbounded (≤) s ↔ unbounded (≤) (s ∩ {b | a < b}) :=
by { convert unbounded_le_iff_unbounded_inter_not_le a, ext, exact lt_iff_not_ge' }

theorem bounded_le_iff_bounded_inter_le [linear_order α] (a : α) :
  bounded (≤) s ↔ bounded (≤) (s ∩ {b | a ≤ b}) :=
begin
  use bounded_of_subset_bounded (set.inter_subset_left s _),
  rw @bounded_le_iff_bounded_inter_lt _ s _ a,
  exact bounded_of_subset_bounded (λ x ⟨hx, hx'⟩, ⟨hx, le_of_lt hx'⟩)
end

theorem unbounded_le_iff_unbounded_inter_le [linear_order α] (a : α) :
  unbounded (≤) s ↔ unbounded (≤) (s ∩ {b | a ≤ b}) :=
begin
  rw [←not_bounded_iff, ←not_bounded_iff, not_iff_not],
  exact bounded_le_iff_bounded_inter_le a
end

/-! #### Less than -/

theorem bounded_lt_iff_bounded_inter_not_lt [semilattice_sup α] (a : α) :
  bounded (<) s ↔ bounded (<) (s ∩ {b | ¬ b < a}) :=
bounded_r_iff_bounded_inter_not_r
  (λ x y, ⟨x ⊔ y, λ z h, h.elim lt_sup_of_lt_left lt_sup_of_lt_right⟩) a

theorem unbounded_lt_iff_unbounded_inter_not_lt [semilattice_sup α] (a : α) :
  unbounded (<) s ↔ unbounded (<) (s ∩ {b | ¬ b < a}) :=
begin
  rw [←not_bounded_iff, ←not_bounded_iff, not_iff_not],
  exact bounded_lt_iff_bounded_inter_not_lt a
end

theorem bounded_lt_iff_bounded_inter_le [linear_order α] (a : α) :
  bounded (<) s ↔ bounded (<) (s ∩ {b | a ≤ b}) :=
by { convert bounded_lt_iff_bounded_inter_not_lt a, ext, exact not_lt.symm }

theorem unbounded_lt_iff_unbounded_inter_le [linear_order α] (a : α) :
  unbounded (<) s ↔ unbounded (<) (s ∩ {b | a ≤ b}) :=
by { convert unbounded_lt_iff_unbounded_inter_not_lt a, ext, exact not_lt.symm }

theorem bounded_lt_iff_bounded_inter_lt [linear_order α] [no_top_order α] (a : α) :
  bounded (<) s ↔ bounded (<) (s ∩ {b | a < b}) :=
begin
  rw [←bounded_le_iff_bounded_lt, ←bounded_le_iff_bounded_lt],
  exact bounded_le_iff_bounded_inter_lt a
end

theorem unbounded_lt_iff_unbounded_inter_lt [linear_order α] [no_top_order α] (a : α) :
  unbounded (<) s ↔ unbounded (<) (s ∩ {b | a < b}) :=
begin
  rw [←not_bounded_iff, ←not_bounded_iff, not_iff_not],
  exact bounded_lt_iff_bounded_inter_lt a
end

/-! #### Greater or equal -/

theorem bounded_ge_iff_bounded_inter_not_ge [semilattice_inf α] (a : α) :
  bounded (≥) s ↔ bounded (≥) (s ∩ {b | ¬ a ≤ b}) :=
bounded_r_iff_bounded_inter_not_r
  (λ x y, ⟨x ⊓ y, λ z h, h.elim inf_le_of_left_le inf_le_of_right_le⟩) a

theorem unbounded_ge_iff_unbounded_inter_not_ge [semilattice_inf α] (a : α) :
  unbounded (≥) s ↔ unbounded (≥) (s ∩ {b | ¬ a ≤ b}) :=
begin
  rw [←not_bounded_iff, ←not_bounded_iff, not_iff_not],
  exact bounded_ge_iff_bounded_inter_not_ge a
end

theorem bounded_ge_iff_bounded_inter_gt [linear_order α] (a : α) :
  bounded (≥) s ↔ bounded (≥) (s ∩ {b | b < a}) :=
by { convert bounded_ge_iff_bounded_inter_not_ge a, ext, exact lt_iff_not_ge' }

theorem unbounded_ge_iff_unbounded_inter_gt [linear_order α] (a : α) :
  unbounded (≥) s ↔ unbounded (≥) (s ∩ {b | b < a}) :=
by { convert unbounded_ge_iff_unbounded_inter_not_ge a, ext, exact lt_iff_not_ge' }

theorem bounded_ge_iff_bounded_inter_ge [linear_order α] (a : α) :
  bounded (≥) s ↔ bounded (≥) (s ∩ {b | b ≤ a}) :=
begin
  use bounded_of_subset_bounded (set.inter_subset_left s _),
  rw @bounded_ge_iff_bounded_inter_gt _ s _ a,
  exact bounded_of_subset_bounded (λ x ⟨hx, hx'⟩, ⟨hx, le_of_lt hx'⟩)
end

theorem unbounded_ge_iff_unbounded_inter_ge [linear_order α] (a : α) :
  unbounded (≥) s ↔ unbounded (≥) (s ∩ {b | b ≤ a}) :=
begin
  rw [←not_bounded_iff, ←not_bounded_iff, not_iff_not],
  exact bounded_ge_iff_bounded_inter_ge a
end

/-! #### Greater than -/

theorem bounded_gt_iff_bounded_inter_not_gt [semilattice_inf α] (a : α) :
  bounded (>) s ↔ bounded (>) (s ∩ {b | ¬ a < b}) :=
bounded_r_iff_bounded_inter_not_r
  (λ x y, ⟨x ⊓ y, λ z h, h.elim inf_lt_of_left_lt inf_lt_of_right_lt⟩) a

theorem unbounded_gt_iff_unbounded_inter_not_gt [semilattice_inf α] (a : α) :
  unbounded (>) s ↔ unbounded (>) (s ∩ {b | ¬ a < b}) :=
begin
  rw [←not_bounded_iff, ←not_bounded_iff, not_iff_not],
  exact bounded_gt_iff_bounded_inter_not_gt a
end

theorem bounded_gt_iff_bounded_inter_ge [linear_order α] (a : α) :
  bounded (>) s ↔ bounded (>) (s ∩ {b | b ≤ a}) :=
by { convert bounded_gt_iff_bounded_inter_not_gt a, ext, exact not_lt.symm }

theorem unbounded_gt_iff_unbounded_inter_ge [linear_order α] (a : α) :
  unbounded (>) s ↔ unbounded (>) (s ∩ {b | b ≤ a}) :=
by { convert unbounded_gt_iff_unbounded_inter_not_gt a, ext, exact not_lt.symm }

theorem bounded_gt_iff_bounded_inter_gt [linear_order α] [no_bot_order α] (a : α) :
  bounded (>) s ↔ bounded (>) (s ∩ {b | b < a}) :=
begin
  rw [←bounded_ge_iff_bounded_gt, ←bounded_ge_iff_bounded_gt],
  exact bounded_ge_iff_bounded_inter_gt a
end

theorem unbounded_gt_iff_unbounded_inter_gt [linear_order α] [no_bot_order α] (a : α) :
  unbounded (>) s ↔ unbounded (>) (s ∩ {b | b < a}) :=
begin
  rw [←not_bounded_iff, ←not_bounded_iff, not_iff_not],
  exact bounded_gt_iff_bounded_inter_gt a
end
