/-
Copyright (c) 2022 Yaël Dillies, Ella Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Ella Yu
-/
import data.finset.prod
import data.fintype.prod

/-!
# Additive energy

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the additive energy of two finsets of a group. This is a central quantity in
additive combinatorics.

## TODO

It's possibly interesting to have
`(s ×ˢ s) ×ˢ t ×ˢ t).filter (λ x : (α × α) × α × α, x.1.1 * x.2.1 = x.1.2 * x.2.2)` (whose `card` is
`multiplicative_energy s t`) as a standalone definition.
-/

section
variables {α : Type*} [partial_order α] {x y : α}

end

variables {α : Type*} [decidable_eq α]

namespace finset
section has_mul
variables [has_mul α] {s s₁ s₂ t t₁ t₂ : finset α}

/-- The multiplicative energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. -/
@[to_additive additive_energy "The additive energy of two finsets `s` and `t` in a group is the
number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`."]
def multiplicative_energy (s t : finset α) : ℕ :=
(((s ×ˢ s) ×ˢ t ×ˢ t).filter $ λ x : (α × α) × α × α, x.1.1 * x.2.1 = x.1.2 * x.2.2).card

@[to_additive additive_energy_mono]
lemma multiplicative_energy_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) :
  multiplicative_energy s₁ t₁ ≤ multiplicative_energy s₂ t₂ :=
card_le_of_subset $ filter_subset_filter _ $ product_subset_product (product_subset_product hs hs) $
  product_subset_product ht ht

@[to_additive additive_energy_mono_left]
lemma multiplicative_energy_mono_left (hs : s₁ ⊆ s₂) :
  multiplicative_energy s₁ t ≤ multiplicative_energy s₂ t :=
multiplicative_energy_mono hs subset.rfl

@[to_additive additive_energy_mono_right]
lemma multiplicative_energy_mono_right (ht : t₁ ⊆ t₂) :
  multiplicative_energy s t₁ ≤ multiplicative_energy s t₂ :=
multiplicative_energy_mono subset.rfl ht

@[to_additive le_additive_energy]
lemma le_multiplicative_energy : s.card * t.card ≤ multiplicative_energy s t :=
begin
  rw ←card_product,
  refine card_le_card_of_inj_on (λ x, ((x.1, x.1), x.2, x.2)) (by simp [←and_imp]) (λ a _ b _, _),
  simp only [prod.mk.inj_iff, and_self, and_imp],
  exact prod.ext,
end

@[to_additive additive_energy_pos]
lemma multiplicative_energy_pos (hs : s.nonempty) (ht : t.nonempty) :
  0 < multiplicative_energy s t :=
(mul_pos hs.card_pos ht.card_pos).trans_le le_multiplicative_energy

variables (s t)

@[simp, to_additive additive_energy_empty_left]
lemma multiplicative_energy_empty_left : multiplicative_energy ∅ t = 0 :=
by simp [multiplicative_energy]

@[simp, to_additive additive_energy_empty_right]
lemma multiplicative_energy_empty_right : multiplicative_energy s ∅ = 0 :=
by simp [multiplicative_energy]

variables {s t}

@[simp, to_additive additive_energy_pos_iff]
lemma multiplicative_energy_pos_iff : 0 < multiplicative_energy s t ↔ s.nonempty ∧ t.nonempty :=
⟨λ h, of_not_not $ λ H, begin
  simp_rw [not_and_distrib, not_nonempty_iff_eq_empty] at H,
  obtain rfl | rfl := H; simpa [nat.not_lt_zero] using h,
end, λ h, multiplicative_energy_pos h.1 h.2⟩

@[simp, to_additive additive_energy_eq_zero_iff]
lemma multiplicative_energy_eq_zero_iff : multiplicative_energy s t = 0 ↔ s = ∅ ∨ t = ∅ :=
by simp [←(nat.zero_le _).not_gt_iff_eq, not_and_distrib]

end has_mul

section comm_monoid
variables [comm_monoid α]

@[to_additive additive_energy_comm]
lemma multiplicative_energy_comm (s t : finset α) :
  multiplicative_energy s t = multiplicative_energy t s :=
begin
  rw [multiplicative_energy, ←finset.card_map (equiv.prod_comm _ _).to_embedding, map_filter],
  simp [-finset.card_map, eq_comm, multiplicative_energy, mul_comm, map_eq_image, function.comp],
end

end comm_monoid

section comm_group
variables [comm_group α] [fintype α] (s t : finset α)

@[simp, to_additive additive_energy_univ_left]
lemma multiplicative_energy_univ_left :
  multiplicative_energy univ t = fintype.card α * t.card ^ 2 :=
begin
  simp only [multiplicative_energy, univ_product_univ, fintype.card, sq, ←card_product],
  set f : α × α × α → (α × α) × α × α := λ x, ((x.1 * x.2.2, x.1 * x.2.1), x.2) with hf,
  have : (↑((univ : finset α) ×ˢ t ×ˢ t) : set (α × α × α)).inj_on f,
  { rintro ⟨a₁, b₁, c₁⟩ h₁ ⟨a₂, b₂, c₂⟩ h₂ h,
    simp_rw prod.ext_iff at h,
    obtain ⟨h, rfl, rfl⟩ := h,
    rw mul_right_cancel h.1 },
  rw [←card_image_of_inj_on this],
  congr' with a,
  simp only [hf, mem_filter, mem_product, mem_univ, true_and, mem_image, exists_prop, prod.exists],
  refine ⟨λ h, ⟨a.1.1 * a.2.2⁻¹, _, _, h.1, by simp [mul_right_comm, h.2]⟩, _⟩,
  rintro ⟨b, c, d, hcd, rfl⟩,
  simpa [mul_right_comm],
end

@[simp, to_additive additive_energy_univ_right]
lemma multiplicative_energy_univ_right :
  multiplicative_energy s univ = fintype.card α * s.card ^ 2 :=
by rw [multiplicative_energy_comm, multiplicative_energy_univ_left]

end comm_group
end finset
