/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton, Floris van Doorn
-/
import order.cover.basic
import data.set.intervals.ord_connected

/-!
# Lemmas about the order covering relation and order connected sets.
-/

open set order_dual

variables {α β : Type*}

section weakly_covers

section preorder
variables [preorder α] [preorder β] {a b c : α}

lemma wcovby.Ioo_eq (h : a ⩿ b) : Ioo a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x hx, h.2 hx.1 hx.2

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

end preorder

section partial_order
variables [partial_order α] {a b c : α}

lemma wcovby.Icc_eq (h : a ⩿ b) : Icc a b = {a, b} :=
by { ext c, exact h.le_and_le_iff }

lemma wcovby.Ico_subset (h : a ⩿ b) : Ico a b ⊆ {a} :=
by rw [← Icc_diff_right, h.Icc_eq, diff_singleton_subset_iff, pair_comm]

lemma wcovby.Ioc_subset (h : a ⩿ b) : Ioc a b ⊆ {b} :=
by rw [← Icc_diff_left, h.Icc_eq, diff_singleton_subset_iff]

end partial_order

end weakly_covers

section preorder
variables [preorder α] [preorder β] {a b c : α}

lemma covby.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅ :=
h.wcovby.Ioo_eq

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
variables [partial_order α] {a b c : α}

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

end linear_order

namespace prod
variables [partial_order α] [partial_order β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

@[simp] lemma swap_wcovby_swap : x.swap ⩿ y.swap ↔ x ⩿ y :=
apply_wcovby_apply_iff (order_iso.prod_comm : α × β ≃o β × α)

@[simp] lemma swap_covby_swap : x.swap ⋖ y.swap ↔ x ⋖ y :=
apply_covby_apply_iff (order_iso.prod_comm : α × β ≃o β × α)

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
