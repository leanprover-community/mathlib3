/-
Copyright (u) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.basic
import data.multiset.sort

/-!
# Majorization
-/

namespace multiset
variables {α : Type*} (r : α → α → Prop) [decidable_rel r] [is_total α r] [is_antisymm α r]
  [is_trans α r]

open function

lemma left_inverse_coe_sort : left_inverse coe (sort r) := λ a, by simp
lemma sort_injective : injective (sort r) := (left_inverse_coe_sort _).injective

end multiset

open list
open_locale big_operators

variables {α : Type*}

section linear_ordered_add_comm_monoid
variables [linear_ordered_add_comm_monoid α] {s t u : multiset α}

-- Why do I need this?
instance linear_ordered_add_comm_monoid.to_decidable_le : @decidable_rel α (≤) :=
linear_order.decidable_le

def weak_majorize (s t : multiset α) : Prop :=
s.card = t.card ∧ ∀ n, ((s.sort (≥)).take n).sum ≤ ((t.sort (≥)).take n).sum

infix ` ≼ʷ `:50 := weak_majorize

def majorize (s t : multiset α) : Prop := s ≼ʷ t ∧ s.sum = t.sum

infix ` ≼ᵐ `:50 := majorize

def strict_majorize (s t : multiset α) : Prop := s ≼ᵐ t ∧ ¬ t ≼ᵐ s

infix ` ≺ᵐ `:50 := strict_majorize

protected lemma majorize.weak_majorize : s ≼ᵐ t → s ≼ʷ t := and.left
protected lemma majorize.card_eq_card (h : s ≼ᵐ t) : s.card = t.card := h.1.1

@[refl] lemma weak_majorize.refl (s : multiset α) : s ≼ʷ s := ⟨rfl, λ n, le_rfl⟩
lemma weak_majorize.rfl : s ≼ʷ s := weak_majorize.refl _

@[refl] lemma majorize.refl (s : multiset α) : s ≼ᵐ s := ⟨weak_majorize.rfl, rfl⟩
lemma majorize.rfl : s ≼ᵐ s := majorize.refl _

lemma strict_majorize.irrefl (s : multiset α) : ¬ s ≺ᵐ s := λ h, h.2 h.1

@[trans] lemma weak_majorize.trans (hst : s ≼ʷ t) (htu : t ≼ʷ u) : s ≼ʷ u :=
⟨hst.1.trans htu.1, λ n, (hst.2 _).trans $ htu.2 _⟩

@[trans] lemma majorize.trans (hst : s ≼ᵐ t) (htu : t ≼ᵐ u) : s ≼ᵐ u :=
⟨hst.1.trans htu.1, hst.2.trans htu.2⟩

end linear_ordered_add_comm_monoid

variables [linear_ordered_cancel_add_comm_monoid α] {s t : multiset α}

-- Why do I need this?
instance linear_ordered_cancel_add_comm_monoid.to_decidable_le : @decidable_rel α (≤) :=
linear_order.decidable_le

lemma weak_majorize.antisymm (hst : s ≼ʷ t) (hts : t ≼ʷ s) : s = t :=
begin
  refine multiset.sort_injective (≥) (list.ext_le (by simp [hst.1]) $ λ n h₀ h₁, _),
  have h := λ n, (hst.2 n).antisymm (hts.2 n),
  simpa only [sum_take_succ _ _ h₀, sum_take_succ _ _ h₁, h n, add_right_inj] using h (n + 1),
end

lemma majorize.antisymm (hst : s ≼ᵐ t) (hts : t ≼ᵐ s) : s = t := hst.1.antisymm hts.1

lemma weak_majorize_antisymm_iff : s = t ↔ s ≼ʷ t ∧ t ≼ʷ s :=
⟨by { rintro rfl, exact ⟨weak_majorize.rfl, weak_majorize.rfl⟩ }, λ h, h.1.antisymm h.2⟩

lemma majorize_antisymm_iff : s = t ↔ s ≼ᵐ t ∧ t ≼ᵐ s :=
⟨by { rintro rfl, exact ⟨majorize.rfl, majorize.rfl⟩ }, λ h, h.1.antisymm h.2⟩

lemma majorize_iff_strict_majorize_or_eq : s ≼ᵐ t ↔ s ≺ᵐ t ∨ s = t :=
by rw [strict_majorize, majorize_antisymm_iff, ←and_or_distrib_left, and_iff_left (em' _)]

alias majorize_iff_strict_majorize_or_eq ↔ majorize.strict_majorize_or_eq _
