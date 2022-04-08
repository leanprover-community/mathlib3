/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton
-/
import data.set.intervals.ord_connected

/-!
# The covering relation

This file defines the covering relation in an order. `b` is said to cover `a` if `a < b` and there
is no element in between. ∃ b, a < b

## Notation

`a ⋖ b` means that `b` covers `a`.
-/

open set

variables {α β : Type*}

section has_lt
variables [has_lt α] {a b : α}

/-- `covby a b` means that `b` covers `a`: `a < b` and there is no element in between. -/
def covby (a b : α) : Prop := a < b ∧ ∀ ⦃c⦄, a < c → ¬ c < b

infix ` ⋖ `:50 := covby

lemma covby.lt (h : a ⋖ b) : a < b := h.1

/-- If `a < b`, then `b` does not cover `a` iff there's an element in between. -/
lemma not_covby_iff (h : a < b) : ¬a ⋖ b ↔ ∃ c, a < c ∧ c < b :=
by { simp_rw [covby, not_and, not_forall, exists_prop, not_not], exact imp_iff_right h }

alias not_covby_iff ↔ exists_lt_lt_of_not_covby _
alias exists_lt_lt_of_not_covby ← has_lt.lt.exists_lt_lt

/-- In a dense order, nothing covers anything. -/
lemma not_covby [densely_ordered α] : ¬ a ⋖ b :=
λ h, let ⟨c, hc⟩ := exists_between h.1 in h.2 hc.1 hc.2

lemma densely_ordered_iff_forall_not_covby : densely_ordered α ↔ ∀ a b : α, ¬ a ⋖ b :=
⟨λ h a b, @not_covby _ _ _ _ h, λ h, ⟨λ a b hab, exists_lt_lt_of_not_covby hab $ h _ _⟩⟩

open order_dual

@[simp] lemma to_dual_covby_to_dual_iff : to_dual b ⋖ to_dual a ↔ a ⋖ b :=
and_congr_right' $ forall_congr $ λ c, forall_swap

@[simp] lemma of_dual_covby_of_dual_iff {a b : order_dual α} :
  of_dual a ⋖ of_dual b ↔ b ⋖ a :=
and_congr_right' $ forall_congr $ λ c, forall_swap

alias to_dual_covby_to_dual_iff ↔ _ covby.to_dual
alias of_dual_covby_of_dual_iff ↔ _ covby.of_dual

end has_lt

section preorder
variables [preorder α] [preorder β] {a b : α} {f : α ↪o β} {e : α ≃o β}

lemma covby.le (h : a ⋖ b) : a ≤ b := h.1.le
protected lemma covby.ne (h : a ⋖ b) : a ≠ b := h.lt.ne
lemma covby.ne' (h : a ⋖ b) : b ≠ a := h.lt.ne'

instance covby.is_irrefl : is_irrefl α (⋖) := ⟨λ a ha, ha.ne rfl⟩

lemma covby.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x hx, h.2 hx.1 hx.2

lemma covby.of_image (h : f a ⋖ f b) : a ⋖ b :=
begin
  refine ⟨_, λ c hac hcb, _⟩,
  { rw ←order_embedding.lt_iff_lt f,
    exact h.1 },
  rw ←order_embedding.lt_iff_lt f at hac hcb,
  exact h.2 hac hcb,
end

lemma covby.image (hab : a ⋖ b) (h : (set.range f).ord_connected) : f a ⋖ f b :=
begin
  refine ⟨f.strict_mono hab.1, λ c ha hb, _⟩,
  obtain ⟨c, rfl⟩ := h.out (mem_range_self _) (mem_range_self _) ⟨ha.le, hb.le⟩,
  rw f.lt_iff_lt at ha hb,
  exact hab.2 ha hb,
end

protected lemma set.ord_connected.image_covby_image_iff (h : (set.range f).ord_connected) :
  f a ⋖ f b ↔ a ⋖ b :=
⟨covby.of_image, λ hab, hab.image h⟩

@[simp] lemma apply_covby_apply_iff : e a ⋖ e b ↔ a ⋖ b :=
⟨covby.of_image, λ hab, begin
  refine ⟨e.strict_mono hab.1, λ c ha hb, _⟩,
  rw [←e.symm.lt_iff_lt, order_iso.symm_apply_apply] at ha hb,
  exact hab.2 ha hb,
end⟩

end preorder

section partial_order
variables [partial_order α] {a b : α}

lemma covby.Ico_eq (h : a ⋖ b) : Ico a b = {a} :=
by rw [←set.Ioo_union_left h.lt, h.Ioo_eq, empty_union]

lemma covby.Ioc_eq (h : a ⋖ b) : Ioc a b = {b} :=
by rw [←set.Ioo_union_right h.lt, h.Ioo_eq, empty_union]

lemma covby.Icc_eq (h : a ⋖ b) : Icc a b = {a, b} :=
by { rw [←set.Ico_union_right h.le, h.Ico_eq], refl }

end partial_order
