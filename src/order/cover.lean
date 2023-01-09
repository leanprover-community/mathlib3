/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton, Floris van Doorn
-/
import data.set.intervals.ord_connected
import order.antisymmetrization

/-!
# The covering relation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
variables [preorder α] [preorder β] {a b c : α}

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

lemma antisymm_rel.wcovby (h : antisymm_rel (≤) a b) : a ⩿ b := wcovby_of_le_of_le h.1 h.2

lemma wcovby.wcovby_iff_le (hab : a ⩿ b) : b ⩿ a ↔ b ≤ a :=
⟨λ h, h.le, λ h, h.wcovby_of_le hab.le⟩

lemma wcovby_of_eq_or_eq (hab : a ≤ b) (h : ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b) : a ⩿ b :=
⟨hab, λ c ha hb, (h c ha.le hb.le).elim ha.ne' hb.ne⟩

lemma antisymm_rel.trans_wcovby (hab : antisymm_rel (≤) a b) (hbc : b ⩿ c) : a ⩿ c :=
⟨hab.1.trans hbc.le, λ d had hdc, hbc.2 (hab.2.trans_lt had) hdc⟩

lemma wcovby_congr_left (hab : antisymm_rel (≤) a b) : a ⩿ c ↔ b ⩿ c :=
⟨hab.symm.trans_wcovby, hab.trans_wcovby⟩

lemma wcovby.trans_antisymm_rel (hab : a ⩿ b) (hbc : antisymm_rel (≤) b c) : a ⩿ c :=
⟨hab.le.trans hbc.1, λ d had hdc, hab.2 had $ hdc.trans_le hbc.2⟩

lemma wcovby_congr_right (hab : antisymm_rel (≤) a b) : c ⩿ a ↔ c ⩿ b :=
⟨λ h, h.trans_antisymm_rel hab, λ h, h.trans_antisymm_rel hab.symm⟩

/-- If `a ≤ b`, then `b` does not cover `a` iff there's an element in between. -/
lemma not_wcovby_iff (h : a ≤ b) : ¬ a ⩿ b ↔ ∃ c, a < c ∧ c < b :=
by simp_rw [wcovby, h, true_and, not_forall, exists_prop, not_not]

instance wcovby.is_refl : is_refl α (⩿) := ⟨wcovby.refl⟩

lemma wcovby.Ioo_eq (h : a ⩿ b) : Ioo a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x hx, h.2 hx.1 hx.2

lemma wcovby_iff_Ioo_eq : a ⩿ b ↔ a ≤ b ∧ Ioo a b = ∅ :=
and_congr_right' $ by simp [eq_empty_iff_forall_not_mem]

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

/-- An `iff` version of `wcovby.eq_or_eq` and `wcovby_of_eq_or_eq`. -/
lemma wcovby_iff_le_and_eq_or_eq : a ⩿ b ↔ a ≤ b ∧ ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b :=
⟨λ h, ⟨h.le, λ c, h.eq_or_eq⟩, and.rec wcovby_of_eq_or_eq⟩

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

section semilattice_sup
variables [semilattice_sup α] {a b c : α}

lemma wcovby.sup_eq (hac : a ⩿ c) (hbc : b ⩿ c) (hab : a ≠ b) : a ⊔ b = c :=
(sup_le hac.le hbc.le).eq_of_not_lt $ λ h,
  hab.lt_sup_or_lt_sup.elim (λ h', hac.2 h' h) (λ h', hbc.2 h' h)

end semilattice_sup

section semilattice_inf
variables [semilattice_inf α] {a b c : α}

lemma wcovby.inf_eq (hca : c ⩿ a) (hcb : c ⩿ b) (hab : a ≠ b) : a ⊓ b = c :=
(le_inf hca.le hcb.le).eq_of_not_gt $ λ h, hab.inf_lt_or_inf_lt.elim (hca.2 h) (hcb.2 h)

end semilattice_inf

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
variables [preorder α] [preorder β] {a b c : α}

lemma covby.le (h : a ⋖ b) : a ≤ b := h.1.le
protected lemma covby.ne (h : a ⋖ b) : a ≠ b := h.lt.ne
lemma covby.ne' (h : a ⋖ b) : b ≠ a := h.lt.ne'

protected lemma covby.wcovby (h : a ⋖ b) : a ⩿ b := ⟨h.le, h.2⟩
lemma wcovby.covby_of_not_le (h : a ⩿ b) (h2 : ¬ b ≤ a) : a ⋖ b := ⟨h.le.lt_of_not_le h2, h.2⟩
lemma wcovby.covby_of_lt (h : a ⩿ b) (h2 : a < b) : a ⋖ b := ⟨h2, h.2⟩

lemma not_covby_of_lt_of_lt (h₁ : a < b) (h₂ : b < c) : ¬ a ⋖ c :=
(not_covby_iff (h₁.trans h₂)).2 ⟨b, h₁, h₂⟩

lemma covby_iff_wcovby_and_lt : a ⋖ b ↔ a ⩿ b ∧ a < b :=
⟨λ h, ⟨h.wcovby, h.lt⟩, λ h, h.1.covby_of_lt h.2⟩

lemma covby_iff_wcovby_and_not_le : a ⋖ b ↔ a ⩿ b ∧ ¬ b ≤ a :=
⟨λ h, ⟨h.wcovby, h.lt.not_le⟩, λ h, h.1.covby_of_not_le h.2⟩

lemma wcovby_iff_covby_or_le_and_le : a ⩿ b ↔ a ⋖ b ∨ (a ≤ b ∧ b ≤ a) :=
⟨λ h, or_iff_not_imp_right.mpr $ λ h', h.covby_of_not_le $ λ hba, h' ⟨h.le, hba⟩,
  λ h', h'.elim (λ h, h.wcovby) (λ h, h.1.wcovby_of_le h.2)⟩

lemma antisymm_rel.trans_covby (hab : antisymm_rel (≤) a b) (hbc : b ⋖ c) : a ⋖ c :=
⟨hab.1.trans_lt hbc.lt, λ d had hdc, hbc.2 (hab.2.trans_lt had) hdc⟩

lemma covby_congr_left (hab : antisymm_rel (≤) a b) : a ⋖ c ↔ b ⋖ c :=
⟨hab.symm.trans_covby, hab.trans_covby⟩

lemma covby.trans_antisymm_rel (hab : a ⋖ b) (hbc : antisymm_rel (≤) b c) : a ⋖ c :=
⟨hab.lt.trans_le hbc.1, λ d had hdb, hab.2 had $ hdb.trans_le hbc.2⟩

lemma covby_congr_right (hab : antisymm_rel (≤) a b) : c ⋖ a ↔ c ⋖ b :=
⟨λ h, h.trans_antisymm_rel hab, λ h, h.trans_antisymm_rel hab.symm⟩

instance : is_nonstrict_strict_order α (⩿) (⋖) :=
⟨λ a b, covby_iff_wcovby_and_not_le.trans $ and_congr_right $ λ h, h.wcovby_iff_le.not.symm⟩

instance covby.is_irrefl : is_irrefl α (⋖) := ⟨λ a ha, ha.ne rfl⟩

lemma covby.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅ :=
h.wcovby.Ioo_eq

lemma covby_iff_Ioo_eq : a ⋖ b ↔ a < b ∧ Ioo a b = ∅ :=
and_congr_right' $ by simp [eq_empty_iff_forall_not_mem]

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

lemma covby_of_eq_or_eq (hab : a < b) (h : ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b) : a ⋖ b :=
⟨hab, λ c ha hb, (h c ha.le hb.le).elim ha.ne' hb.ne⟩

end preorder

section partial_order
variables [partial_order α] {a b c : α}

lemma wcovby.covby_of_ne (h : a ⩿ b) (h2 : a ≠ b) : a ⋖ b := ⟨h.le.lt_of_ne h2, h.2⟩

lemma covby_iff_wcovby_and_ne : a ⋖ b ↔ a ⩿ b ∧ a ≠ b :=
⟨λ h, ⟨h.wcovby, h.ne⟩, λ h, h.1.covby_of_ne h.2⟩

lemma wcovby_iff_covby_or_eq : a ⩿ b ↔ a ⋖ b ∨ a = b :=
by rw [le_antisymm_iff, wcovby_iff_covby_or_le_and_le]

lemma wcovby_iff_eq_or_covby : a ⩿ b ↔ a = b ∨ a ⋖ b := wcovby_iff_covby_or_eq.trans or.comm

alias wcovby_iff_covby_or_eq ↔ wcovby.covby_or_eq _
alias wcovby_iff_eq_or_covby ↔ wcovby.eq_or_covby _

lemma covby.eq_or_eq (h : a ⋖ b) (h2 : a ≤ c) (h3 : c ≤ b) : c = a ∨ c = b :=
h.wcovby.eq_or_eq h2 h3

/-- An `iff` version of `covby.eq_or_eq` and `covby_of_eq_or_eq`. -/
lemma covby_iff_lt_and_eq_or_eq : a ⋖ b ↔ a < b ∧ ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b :=
⟨λ h, ⟨h.lt, λ c, h.eq_or_eq⟩, and.rec covby_of_eq_or_eq⟩

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

/-- If `a`, `b`, `c` are consecutive and `a < x < c` then `x = b`. -/
lemma covby.eq_of_between {x : α} (hab : a ⋖ b) (hbc : b ⋖ c) (hax : a < x) (hxc : x < c) :
  x = b :=
le_antisymm (le_of_not_lt $ λ h, hbc.2 h hxc) (le_of_not_lt $ hab.2 hax)

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

namespace prod
variables [partial_order α] [partial_order β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

@[simp] lemma swap_wcovby_swap : x.swap ⩿ y.swap ↔ x ⩿ y :=
apply_wcovby_apply_iff (order_iso.prod_comm : α × β ≃o β × α)

@[simp] lemma swap_covby_swap : x.swap ⋖ y.swap ↔ x ⋖ y :=
apply_covby_apply_iff (order_iso.prod_comm : α × β ≃o β × α)

lemma fst_eq_or_snd_eq_of_wcovby : x ⩿ y → x.1 = y.1 ∨ x.2 = y.2 :=
begin
  refine λ h, of_not_not (λ hab, _),
  push_neg at hab,
  exact h.2 (mk_lt_mk.2 $ or.inl ⟨hab.1.lt_of_le h.1.1, le_rfl⟩)
    (mk_lt_mk.2 $ or.inr ⟨le_rfl, hab.2.lt_of_le h.1.2⟩),
end

lemma _root_.wcovby.fst (h : x ⩿ y) : x.1 ⩿ y.1 :=
⟨h.1.1, λ c h₁ h₂, h.2 (mk_lt_mk_iff_left.2 h₁) ⟨⟨h₂.le, h.1.2⟩, λ hc, h₂.not_le hc.1⟩⟩

lemma _root_.wcovby.snd (h : x ⩿ y) : x.2 ⩿ y.2 :=
⟨h.1.2, λ c h₁ h₂, h.2 (mk_lt_mk_iff_right.2 h₁) ⟨⟨h.1.1, h₂.le⟩, λ hc, h₂.not_le hc.2⟩⟩

lemma mk_wcovby_mk_iff_left : (a₁, b) ⩿ (a₂, b) ↔ a₁ ⩿ a₂ :=
begin
  refine ⟨wcovby.fst, and.imp mk_le_mk_iff_left.2 $ λ h c h₁ h₂, _⟩,
  have : c.2 = b:= h₂.le.2.antisymm h₁.le.2,
  rw [←@prod.mk.eta _ _ c, this, mk_lt_mk_iff_left] at h₁ h₂,
  exact h h₁ h₂,
end

lemma mk_wcovby_mk_iff_right : (a, b₁) ⩿ (a, b₂) ↔ b₁ ⩿ b₂ :=
swap_wcovby_swap.trans mk_wcovby_mk_iff_left

lemma mk_covby_mk_iff_left : (a₁, b) ⋖ (a₂, b) ↔ a₁ ⋖ a₂ :=
by simp_rw [covby_iff_wcovby_and_lt, mk_wcovby_mk_iff_left, mk_lt_mk_iff_left]

lemma mk_covby_mk_iff_right : (a, b₁) ⋖ (a, b₂) ↔ b₁ ⋖ b₂ :=
by simp_rw [covby_iff_wcovby_and_lt, mk_wcovby_mk_iff_right, mk_lt_mk_iff_right]

lemma mk_wcovby_mk_iff : (a₁, b₁) ⩿ (a₂, b₂) ↔ a₁ ⩿ a₂ ∧ b₁ = b₂ ∨ b₁ ⩿ b₂ ∧ a₁ = a₂ :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain rfl | rfl : a₁ = a₂ ∨ b₁ = b₂ := fst_eq_or_snd_eq_of_wcovby h,
    { exact or.inr ⟨mk_wcovby_mk_iff_right.1 h, rfl⟩ },
    { exact or.inl ⟨mk_wcovby_mk_iff_left.1 h, rfl⟩ } },
  { rintro (⟨h, rfl⟩ | ⟨h, rfl⟩),
    { exact mk_wcovby_mk_iff_left.2 h },
    { exact mk_wcovby_mk_iff_right.2 h } }
end

lemma mk_covby_mk_iff : (a₁, b₁) ⋖ (a₂, b₂) ↔ a₁ ⋖ a₂ ∧ b₁ = b₂ ∨ b₁ ⋖ b₂ ∧ a₁ = a₂ :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain rfl | rfl : a₁ = a₂ ∨ b₁ = b₂ := fst_eq_or_snd_eq_of_wcovby h.wcovby,
    { exact or.inr ⟨mk_covby_mk_iff_right.1 h, rfl⟩ },
    { exact or.inl ⟨mk_covby_mk_iff_left.1 h, rfl⟩ } },
  { rintro (⟨h, rfl⟩ | ⟨h, rfl⟩),
    { exact mk_covby_mk_iff_left.2 h },
    { exact mk_covby_mk_iff_right.2 h } }
end

lemma wcovby_iff : x ⩿ y ↔ x.1 ⩿ y.1 ∧ x.2 = y.2 ∨ x.2 ⩿ y.2 ∧ x.1 = y.1 :=
by { cases x, cases y, exact mk_wcovby_mk_iff }

lemma covby_iff : x ⋖ y ↔ x.1 ⋖ y.1 ∧ x.2 = y.2 ∨ x.2 ⋖ y.2 ∧ x.1 = y.1 :=
by { cases x, cases y, exact mk_covby_mk_iff }

end prod
