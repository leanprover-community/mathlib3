/-
Copyright (c) 2022 Yaël Dillies Ella Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies Ella Yu
-/
import data.finset.pointwise

-- TODO: Change to explicit
attribute [simp] set.preimage_swap_prod set.image_swap_prod

namespace finset
variables {α β : Type*} {f : α ≃ β} {s : finset α} {t : finset β}

-- TODO: Rename `map_filter` to `filter_map`
lemma map_filter' {p : α → Prop} [decidable_pred p] :
  (s.filter p).map f.to_embedding = (s.map f.to_embedding).filter (p ∘ f.symm) :=
by simp only [map_filter, function.comp, equiv.to_embedding_apply, equiv.symm_apply_apply]

variables [decidable_eq α] [decidable_eq β]

@[simp] lemma image_swap_prod (s : finset α) (t : finset β) : (t ×ˢ s).image prod.swap = s ×ˢ t :=
coe_injective $ by { push_cast, exact set.image_swap_prod }

end finset

namespace equiv
variables {α β : Type*}

@[simp] lemma coe_to_embedding (f : α ≃ β) : ⇑f.to_embedding = f := rfl

@[simp] lemma coe_prod_comm : ⇑(equiv.prod_comm α β) = prod.swap := rfl

end equiv

noncomputable theory

open finset
open_locale pointwise

variables {α β : Type*} [add_comm_group α] [add_comm_group β] [decidable_eq α] [decidable_eq β]
  {A B C s s₁ s₂ t t₁ t₂ : finset α} {X Y Z : finset β}

def additive_energy (A B : finset α) : ℕ :=
(((A ×ˢ A) ×ˢ (B ×ˢ B)).filter $
  λ (x : (α × α) × (α × α)), x.1.1 + x.2.1 = x.1.2 + x.2.2).card

lemma additive_energy_comm (A B : finset α) : additive_energy A B = additive_energy B A :=
begin
  rw [additive_energy, ←finset.card_map (equiv.prod_comm _ _).to_embedding, map_filter'],
  simp [-finset.card_map, eq_comm, additive_energy, add_comm, map_eq_image, function.comp],
end

lemma additive_energy_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) :
  additive_energy s₁ t₁ ≤ additive_energy s₂ t₂ :=
card_le_of_subset $ filter_subset_filter _ $ product_subset_product (product_subset_product hs hs) $
  product_subset_product ht ht

lemma additive_energy_mono_left (hs : s₁ ⊆ s₂) : additive_energy s₁ t ≤ additive_energy s₂ t :=
additive_energy_mono hs subset.rfl

lemma additive_energy_mono_right (ht : t₁ ⊆ t₂) : additive_energy s t₁ ≤ additive_energy s t₂ :=
additive_energy_mono subset.rfl ht
