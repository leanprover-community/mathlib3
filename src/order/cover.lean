/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton, Floris van Doorn
-/
import data.set.intervals.ord_connected

/-!
# The covering relation

This file defines the covering relation in an order. `b` is said to cover `a` if `a < b` and there
is no element in between. We say that `b` weakly covers `a` if `a ≤ b` and there is no element
between `a` and `b`. In a partial order this is equivalent to `a ⋖ b ∨ a = b`, in a preorder this
is equivalent to `a ⋖ b ∨ (a ≤ b ∧ b ≤ a)`

## Notation

* `a ⋖ b` means that `b` covers `a`.
* `a ⩿ b` means that `b` weakly covers `a`.
-/

open set order_dual

variables {α β : Type*}

section weakly_covers

section preorder
variables [preorder α] [preorder β] {a b c: α}

/-- `wcovby a b` means that `a = b` or `b` covers `a`.
This means that `a ≤ b` and there is no element in between.
-/
def wcovby (a b : α) : Prop := a ≤ b ∧ ∀ ⦃c⦄, a < c → ¬ c < b

infix ` ⩿ `:50 := wcovby

lemma wcovby.le (h : a ⩿ b) : a ≤ b := h.1

lemma wcovby.refl (a : α) : a ⩿ a := ⟨le_rfl, λ c hc, hc.not_lt⟩
lemma wcovby.rfl : a ⩿ a := wcovby.refl a

protected lemma eq.wcovby (h : a = b) : a ⩿ b := h ▸ wcovby.rfl

lemma wcovby_of_le_of_le (h1 : a ≤ b) (h2 : b ≤ a) : a ⩿ b :=
⟨h1, λ c hac hcb, (hac.trans hcb).not_le h2⟩

alias wcovby_of_le_of_le ← has_le.le.wcovby_of_le

lemma wcovby.wcovby_iff_le (hab : a ⩿ b) : b ⩿ a ↔ b ≤ a :=
⟨λ h, h.le, λ h, h.wcovby_of_le hab.le⟩

lemma wcovby_of_eq_or_eq (hab : a ≤ b) (h : ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b) : a ⩿ b :=
⟨hab, λ c ha hb, (h c ha.le hb.le).elim ha.ne' hb.ne⟩

/-- If `a ≤ b`, then `b` does not cover `a` iff there's an element in between. -/
lemma not_wcovby_iff (h : a ≤ b) : ¬ a ⩿ b ↔ ∃ c, a < c ∧ c < b :=
by simp_rw [wcovby, h, true_and, not_forall, exists_prop, not_not]

instance wcovby.is_refl : is_refl α (⩿) := ⟨wcovby.refl⟩

lemma wcovby.Ioo_eq (h : a ⩿ b) : Ioo a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x hx, h.2 hx.1 hx.2

lemma wcovby.of_image (f : α ↪o β) (h : f a ⩿ f b) : a ⩿ b :=
⟨f.le_iff_le.mp h.le, λ c hac hcb, h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩

lemma wcovby.image (f : α ↪o β) (hab : a ⩿ b) (h : (range f).ord_connected) : f a ⩿ f b :=
begin
  refine ⟨f.monotone hab.le, λ c ha hb, _⟩,
  obtain ⟨c, rfl⟩ := h.out (mem_range_self _) (mem_range_self _) ⟨ha.le, hb.le⟩,
  rw f.lt_iff_lt at ha hb,
  exact hab.2 ha hb,
end

lemma set.ord_connected.apply_wcovby_apply_iff (f : α ↪o β) (h : (range f).ord_connected) :
  f a ⩿ f b ↔ a ⩿ b :=
⟨λ h2, h2.of_image f, λ hab, hab.image f h⟩

@[simp] lemma apply_wcovby_apply_iff {E : Type*} [order_iso_class E α β] (e : E) :
  e a ⩿ e b ↔ a ⩿ b :=
(ord_connected_range (e : α ≃o β)).apply_wcovby_apply_iff ((e : α ≃o β) : α ↪o β)

@[simp] lemma to_dual_wcovby_to_dual_iff : to_dual b ⩿ to_dual a ↔ a ⩿ b :=
and_congr_right' $ forall_congr $ λ c, forall_swap

@[simp] lemma of_dual_wcovby_of_dual_iff {a b : αᵒᵈ} :
  of_dual a ⩿ of_dual b ↔ b ⩿ a :=
and_congr_right' $ forall_congr $ λ c, forall_swap

alias to_dual_wcovby_to_dual_iff ↔ _ wcovby.to_dual
alias of_dual_wcovby_of_dual_iff ↔ _ wcovby.of_dual

end preorder

section partial_order
variables [partial_order α] {a b c : α}

lemma wcovby.eq_or_eq (h : a ⩿ b) (h2 : a ≤ c) (h3 : c ≤ b) : c = a ∨ c = b :=
begin
  rcases h2.eq_or_lt with h2|h2, { exact or.inl h2.symm },
  rcases h3.eq_or_lt with h3|h3, { exact or.inr h3 },
  exact (h.2 h2 h3).elim
end

lemma wcovby.le_and_le_iff (h : a ⩿ b) : a ≤ c ∧ c ≤ b ↔ c = a ∨ c = b :=
begin
  refine ⟨λ h2, h.eq_or_eq h2.1 h2.2, _⟩, rintro (rfl|rfl), exacts [⟨le_rfl, h.le⟩, ⟨h.le, le_rfl⟩]
end

lemma wcovby.Icc_eq (h : a ⩿ b) : Icc a b = {a, b} :=
by { ext c, exact h.le_and_le_iff }

lemma wcovby.Ico_subset (h : a ⩿ b) : Ico a b ⊆ {a} :=
by rw [← Icc_diff_right, h.Icc_eq, diff_singleton_subset_iff, pair_comm]

lemma wcovby.Ioc_subset (h : a ⩿ b) : Ioc a b ⊆ {b} :=
by rw [← Icc_diff_left, h.Icc_eq, diff_singleton_subset_iff]

end partial_order

end weakly_covers

section has_lt
variables [has_lt α] {a b : α}

/-- `covby a b` means that `b` covers `a`: `a < b` and there is no element in between. -/
def covby (a b : α) : Prop := a < b ∧ ∀ ⦃c⦄, a < c → ¬ c < b

infix ` ⋖ `:50 := covby

lemma covby.lt (h : a ⋖ b) : a < b := h.1

/-- If `a < b`, then `b` does not cover `a` iff there's an element in between. -/
lemma not_covby_iff (h : a < b) : ¬a ⋖ b ↔ ∃ c, a < c ∧ c < b :=
by simp_rw [covby, h, true_and, not_forall, exists_prop, not_not]

alias not_covby_iff ↔ exists_lt_lt_of_not_covby _
alias exists_lt_lt_of_not_covby ← has_lt.lt.exists_lt_lt

/-- In a dense order, nothing covers anything. -/
lemma not_covby [densely_ordered α] : ¬ a ⋖ b :=
λ h, let ⟨c, hc⟩ := exists_between h.1 in h.2 hc.1 hc.2

lemma densely_ordered_iff_forall_not_covby : densely_ordered α ↔ ∀ a b : α, ¬ a ⋖ b :=
⟨λ h a b, @not_covby _ _ _ _ h, λ h, ⟨λ a b hab, exists_lt_lt_of_not_covby hab $ h _ _⟩⟩

@[simp] lemma to_dual_covby_to_dual_iff : to_dual b ⋖ to_dual a ↔ a ⋖ b :=
and_congr_right' $ forall_congr $ λ c, forall_swap

@[simp] lemma of_dual_covby_of_dual_iff {a b : αᵒᵈ} : of_dual a ⋖ of_dual b ↔ b ⋖ a :=
and_congr_right' $ forall_congr $ λ c, forall_swap

alias to_dual_covby_to_dual_iff ↔ _ covby.to_dual
alias of_dual_covby_of_dual_iff ↔ _ covby.of_dual

end has_lt

section preorder
variables [preorder α] [preorder β] {a b : α}

lemma covby.le (h : a ⋖ b) : a ≤ b := h.1.le
protected lemma covby.ne (h : a ⋖ b) : a ≠ b := h.lt.ne
lemma covby.ne' (h : a ⋖ b) : b ≠ a := h.lt.ne'

protected lemma covby.wcovby (h : a ⋖ b) : a ⩿ b := ⟨h.le, h.2⟩
lemma wcovby.covby_of_not_le (h : a ⩿ b) (h2 : ¬ b ≤ a) : a ⋖ b := ⟨h.le.lt_of_not_le h2, h.2⟩
lemma wcovby.covby_of_lt (h : a ⩿ b) (h2 : a < b) : a ⋖ b := ⟨h2, h.2⟩

lemma covby_iff_wcovby_and_lt : a ⋖ b ↔ a ⩿ b ∧ a < b :=
⟨λ h, ⟨h.wcovby, h.lt⟩, λ h, h.1.covby_of_lt h.2⟩

lemma covby_iff_wcovby_and_not_le : a ⋖ b ↔ a ⩿ b ∧ ¬ b ≤ a :=
⟨λ h, ⟨h.wcovby, h.lt.not_le⟩, λ h, h.1.covby_of_not_le h.2⟩

lemma wcovby_iff_covby_or_le_and_le : a ⩿ b ↔ a ⋖ b ∨ (a ≤ b ∧ b ≤ a) :=
⟨λ h, or_iff_not_imp_right.mpr $ λ h', h.covby_of_not_le $ λ hba, h' ⟨h.le, hba⟩,
  λ h', h'.elim (λ h, h.wcovby) (λ h, h.1.wcovby_of_le h.2)⟩

instance : is_nonstrict_strict_order α (⩿) (⋖) :=
⟨λ a b, covby_iff_wcovby_and_not_le.trans $ and_congr_right $ λ h, h.wcovby_iff_le.not.symm⟩

instance covby.is_irrefl : is_irrefl α (⋖) := ⟨λ a ha, ha.ne rfl⟩

lemma covby.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅ :=
h.wcovby.Ioo_eq

lemma covby.of_image (f : α ↪o β) (h : f a ⋖ f b) : a ⋖ b :=
⟨f.lt_iff_lt.mp h.lt, λ c hac hcb, h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩

lemma covby.image (f : α ↪o β) (hab : a ⋖ b) (h : (range f).ord_connected) : f a ⋖ f b :=
(hab.wcovby.image f h).covby_of_lt $ f.strict_mono hab.lt

lemma set.ord_connected.apply_covby_apply_iff (f : α ↪o β) (h : (range f).ord_connected) :
  f a ⋖ f b ↔ a ⋖ b :=
⟨covby.of_image f, λ hab, hab.image f h⟩

@[simp] lemma apply_covby_apply_iff {E : Type*} [order_iso_class E α β] (e : E) :
  e a ⋖ e b ↔ a ⋖ b :=
(ord_connected_range (e : α ≃o β)).apply_covby_apply_iff ((e : α ≃o β) : α ↪o β)

end preorder

section partial_order
variables [partial_order α] {a b : α}

lemma wcovby.covby_of_ne (h : a ⩿ b) (h2 : a ≠ b) : a ⋖ b := ⟨h.le.lt_of_ne h2, h.2⟩

lemma covby_iff_wcovby_and_ne : a ⋖ b ↔ a ⩿ b ∧ a ≠ b :=
⟨λ h, ⟨h.wcovby, h.ne⟩, λ h, h.1.covby_of_ne h.2⟩

lemma wcovby_iff_covby_or_eq : a ⩿ b ↔ a ⋖ b ∨ a = b :=
by rw [le_antisymm_iff, wcovby_iff_covby_or_le_and_le]

lemma covby.Ico_eq (h : a ⋖ b) : Ico a b = {a} :=
by rw [←Ioo_union_left h.lt, h.Ioo_eq, empty_union]

lemma covby.Ioc_eq (h : a ⋖ b) : Ioc a b = {b} :=
by rw [←Ioo_union_right h.lt, h.Ioo_eq, empty_union]

lemma covby.Icc_eq (h : a ⋖ b) : Icc a b = {a, b} :=
h.wcovby.Icc_eq

end partial_order

section linear_order
variables [linear_order α] {a b c : α}

lemma covby.Ioi_eq (h : a ⋖ b) : Ioi a = Ici b :=
by rw [← Ioo_union_Ici_eq_Ioi h.lt, h.Ioo_eq, empty_union]

lemma covby.Iio_eq (h : a ⋖ b) : Iio b = Iic a :=
by rw [← Iic_union_Ioo_eq_Iio h.lt, h.Ioo_eq, union_empty]

lemma wcovby.le_of_lt (hab : a ⩿ b) (hcb : c < b) : c ≤ a := not_lt.1 $ λ hac, hab.2 hac hcb
lemma wcovby.ge_of_gt (hab : a ⩿ b) (hac : a < c) : b ≤ c := not_lt.1 $ hab.2 hac
lemma covby.le_of_lt (hab : a ⋖ b) : c < b → c ≤ a := hab.wcovby.le_of_lt
lemma covby.ge_of_gt (hab : a ⋖ b) : a < c → b ≤ c := hab.wcovby.ge_of_gt

lemma covby.unique_left (ha : a ⋖ c) (hb : b ⋖ c) : a = b :=
(hb.le_of_lt ha.lt).antisymm $ ha.le_of_lt hb.lt

lemma covby.unique_right (hb : a ⋖ b) (hc : a ⋖ c) : b = c :=
(hb.ge_of_gt hc.lt).antisymm $ hc.ge_of_gt hb.lt

end linear_order

namespace set

lemma wcovby_insert (x : α) (s : set α) : s ⩿ insert x s :=
begin
  refine wcovby_of_eq_or_eq (subset_insert x s) (λ t hst h2t, _),
  by_cases h : x ∈ t,
  { exact or.inr (subset_antisymm h2t $ insert_subset.mpr ⟨h, hst⟩) },
  { refine or.inl (subset_antisymm _ hst),
    rwa [← diff_singleton_eq_self h, diff_singleton_subset_iff] }
end

lemma covby_insert {x : α} {s : set α} (hx : x ∉ s) : s ⋖ insert x s :=
(wcovby_insert x s).covby_of_lt $ ssubset_insert hx

end set
