/-
Copyright (c) 2022 Yaël Dillies Ella Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies Ella Yu
-/
import data.finset.prod

/-!
# Additive energy

This file defines the additive energy of two finsets of a group. This is a central quantity in
additive combinatorics.
-/

variables {α : Type*} [decidable_eq α]

namespace finset
section has_mul
variables [has_mul α] {s s₁ s₂ t t₁ t₂ : finset α}

/-- The multiplicative energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, b₁, a₂, b₂) ∈ s × t × s × t` such that `a₁ * b₁ = a₂ * b₂`. -/
@[to_additive additive_energy "The additive energy of two finsets `s` and `t` in a group is the
number of quadruples
`(a₁, b₁, a₂, b₂) ∈ s × t × s × t` such that `a₁ + b₁ = a₂ + b₂`."]
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

end has_mul

variables [comm_monoid α]

@[to_additive additive_energy_comm]
lemma multiplicative_energy_comm (s t : finset α) :
  multiplicative_energy s t = multiplicative_energy t s :=
begin
  rw [multiplicative_energy, ←finset.card_map (equiv.prod_comm _ _).to_embedding, map_filter],
  simp [-finset.card_map, eq_comm, multiplicative_energy, mul_comm, map_eq_image, function.comp],
end

end finset
