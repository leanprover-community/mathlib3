/-
Copyright (c) 2023 Yaël Dillies, Vladimir Ivanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Ivanov
-/
import algebra.big_operators.ring
import data.finset.sups
import data.fintype.powerset
import tactic.field_simp
import tactic.ring

/-!
# The Ahlswede-Zhang identity

This file proves the Ahlswede-Zhang identity, which is a nontrivial relation between

## Main declarations

* `finset.truncated_sup`
* `finset.truncated_inf`
-/

open_locale finset_family

namespace finset
variables {α β : Type*}

/-! ### Truncated supremum, truncated infimum -/

section semilattice_sup
variables [semilattice_sup α] [bounded_order α] [@decidable_rel α (≤)]
  [semilattice_sup β] [bounded_order β] [@decidable_rel β (≤)] {s t : finset α} {a b : α}

/-- The infimum of the elements of `s` less than `a` if there are some, otherwise `⊤`. -/
def truncated_sup (s : finset α) (a : α) : α :=
if a ∈ lower_closure (s : set α) then (s.filter $ λ b, a ≤ b).sup id else ⊤

lemma truncated_sup_of_mem (h : a ∈ lower_closure (s : set α)) :
  truncated_sup s a = (s.filter $ λ b, a ≤ b).sup id := if_pos h

lemma truncated_sup_of_not_mem (h : a ∉ lower_closure (s : set α)) :
  truncated_sup s a = ⊤ := if_neg h

@[simp] lemma truncated_sup_empty (a : α) : truncated_sup ∅ a = ⊤ :=
truncated_sup_of_not_mem $ by simp

lemma le_truncated_sup : a ≤ truncated_sup s a :=
begin
  rw truncated_sup,
  split_ifs,
  { obtain ⟨ℬ, hb, h⟩ := h,
    exact h.trans (le_sup $ mem_filter.2 ⟨hb, h⟩) },
  { exact le_top }
end

lemma map_truncated_sup (e : α ≃o β) (s : finset α) (a : α) :
  e (truncated_sup s a) = truncated_sup (s.map e.to_equiv.to_embedding) (e a) :=
begin
  rw [truncated_sup, truncated_sup, apply_ite e, map_finset_sup, map_top],
  congr; simp [filter_map, function.comp],
end

variables [decidable_eq α]

lemma truncated_sup_union (hs : a ∈ lower_closure (s : set α))
  (ht : a ∈ lower_closure (t : set α)) :
  truncated_sup (s ∪ t) a = truncated_sup s a ⊔ truncated_sup t a :=
begin
  rw [truncated_sup_of_mem hs, truncated_sup_of_mem ht,
    truncated_sup_of_mem, filter_union, sup_union],
  rw [coe_union, lower_closure_union],
  exact or.inl hs,
end

lemma truncated_sup_union_left (hs : a ∈ lower_closure (s : set α))
  (ht : a ∉ lower_closure (t : set α)) :
  truncated_sup (s ∪ t) a = truncated_sup s a :=
begin
  simp only [mem_lower_closure, mem_coe, exists_prop, not_exists, not_and] at ht,
  rw [truncated_sup_of_mem, truncated_sup_of_mem hs, filter_union, filter_false_of_mem ht,
    union_empty],
  rw [coe_union, lower_closure_union],
  exact or.inl hs,
end

lemma truncated_sup_union_right (hs : a ∉ lower_closure (s : set α))
  (ht : a ∈ lower_closure (t : set α)) :
  truncated_sup (s ∪ t) a = truncated_sup t a :=
by rw [union_comm, truncated_sup_union_left ht hs]

lemma truncated_sup_union_of_not_mem (hs : a ∉ lower_closure (s : set α))
  (ht : a ∉ lower_closure (t : set α)) :
  truncated_sup (s ∪ t) a = ⊤ :=
truncated_sup_of_not_mem $ by { rw [coe_union, lower_closure_union], exact λ h, h.elim hs ht }

end semilattice_sup

section semilattice_inf
variables [semilattice_inf α] [bounded_order α] [@decidable_rel α (≤)]
  [semilattice_inf β] [bounded_order β] [@decidable_rel β (≤)] {s t : finset α} {a : α}

/-- The infimum of the elements of `s` less than `a` if there are some, otherwise `⊥`. -/
def truncated_inf (s : finset α) (a : α) : α :=
if a ∈ upper_closure (s : set α) then (s.filter $ λ b, b ≤ a).inf id else ⊥

lemma truncated_inf_of_mem (h : a ∈ upper_closure (s : set α)) :
  truncated_inf s a = (s.filter $ λ b, b ≤ a).inf id := if_pos h

lemma truncated_inf_of_not_mem (h : a ∉ upper_closure (s : set α)) :
  truncated_inf s a = ⊥ := if_neg h

lemma truncated_inf_le (s : finset α) (a : α) : truncated_inf s a ≤ a :=
begin
  unfold truncated_inf,
  split_ifs,
  { obtain ⟨ℬ, hb, h⟩ := h,
    exact (inf_le $ mem_filter.2 ⟨hb, h⟩).trans h },
  { exact bot_le }
end

@[simp] lemma truncated_inf_empty (a : α) : truncated_inf ∅ a = ⊥ :=
truncated_inf_of_not_mem $ by simp

lemma map_truncated_inf (e : α ≃o β) (s : finset α) (a : α) :
  e (truncated_inf s a) = truncated_inf (s.map e.to_equiv.to_embedding) (e a) :=
begin
  rw [truncated_inf, truncated_inf, apply_ite e, map_finset_inf, map_bot],
  congr; simp [filter_map, function.comp],
end

variables [decidable_eq α]

lemma truncated_inf_union (hs : a ∈ upper_closure (s : set α))
  (ht : a ∈ upper_closure (t : set α)) :
  truncated_inf (s ∪ t) a = truncated_inf s a ⊓ truncated_inf t a :=
begin
  rw [truncated_inf_of_mem hs, truncated_inf_of_mem ht, truncated_inf_of_mem, filter_union,
    inf_union],
  rw [coe_union, upper_closure_union],
  exact or.inl hs,
end

lemma truncated_inf_union_left (hs : a ∈ upper_closure (s : set α))
  (ht : a ∉ upper_closure (t : set α)) :
  truncated_inf (s ∪ t) a = truncated_inf s a :=
begin
  simp only [mem_upper_closure, mem_coe, exists_prop, not_exists, not_and] at ht,
  rw [truncated_inf_of_mem, truncated_inf_of_mem hs, filter_union,
    filter_false_of_mem ht, union_empty],
  rw [coe_union, upper_closure_union],
  exact or.inl hs,
end

lemma truncated_inf_union_right (hs : a ∉ upper_closure (s : set α))
  (ht : a ∈ upper_closure (t : set α)) :
  truncated_inf (s ∪ t) a = truncated_inf t a :=
by rw [union_comm, truncated_inf_union_left ht hs]

lemma truncated_inf_union_of_not_mem (hs : a ∉ upper_closure (s : set α))
  (ht : a ∉ upper_closure (t : set α)) :
  truncated_inf (s ∪ t) a = ⊥ :=
truncated_inf_of_not_mem $ by { rw [coe_union, upper_closure_union], exact λ h, h.elim hs ht }

end semilattice_inf

section distrib_lattice
variables [distrib_lattice α] [bounded_order α] [decidable_eq α] [@decidable_rel α (≤)]
  {s t : finset α} {a : α}

lemma truncated_sup_infs (hs : a ∈ lower_closure (s : set α)) (ht : a ∈ lower_closure (t : set α)) :
  truncated_sup (s ⊼ t) a = truncated_sup s a ⊓ truncated_sup t a :=
begin
  rw [truncated_sup_of_mem hs, truncated_sup_of_mem ht,
    truncated_sup_of_mem, sup_inf_sup, filter_infs_ge, ←image_inf_product, sup_image],
  refl,
  { rw [coe_infs, lower_closure_infs],
    exact ⟨hs, ht⟩ }
end

lemma truncated_inf_sups (hs : a ∈ upper_closure (s : set α)) (ht : a ∈ upper_closure (t : set α)) :
  truncated_inf (s ⊻ t) a = truncated_inf s a ⊔ truncated_inf t a :=
begin
  rw [truncated_inf_of_mem hs, truncated_inf_of_mem ht,
    truncated_inf_of_mem, inf_sup_inf, filter_sups_le, ←image_sup_product, inf_image],
  refl,
  { rw [coe_sups, upper_closure_sups],
    exact ⟨hs, ht⟩ }
end

lemma truncated_sup_infs_of_not_mem (ha : a ∉ lower_closure (s : set α) ⊓ lower_closure t) :
  truncated_sup (s ⊼ t) a = ⊤ :=
truncated_sup_of_not_mem $ by rwa [coe_infs, lower_closure_infs]

lemma truncated_inf_sups_of_not_mem (ha : a ∉ upper_closure (s : set α) ⊔ upper_closure t) :
  truncated_inf (s ⊻ t) a = ⊥ :=
truncated_inf_of_not_mem $ by rwa [coe_sups, upper_closure_sups]

end distrib_lattice

section boolean_algebra
variables [boolean_algebra α] [@decidable_rel α (≤)] {s : finset α} {a : α}

@[simp] lemma compl_truncated_sup (s : finset α) (a : α) :
  (truncated_sup s a)ᶜ = truncated_inf (s.map ⟨compl, compl_injective⟩) aᶜ :=
map_truncated_sup (order_iso.compl α) _ _

@[simp] lemma compl_truncated_inf (s : finset α) (a : α) :
  (truncated_inf s a)ᶜ = truncated_sup (s.map ⟨compl, compl_injective⟩) aᶜ :=
map_truncated_inf (order_iso.compl α) _ _

end boolean_algebra

variables [decidable_eq α] [fintype α] {s t : finset α}

lemma card_truncated_sup_union_add_card_truncated_sup_infs (𝒜 ℬ : finset (finset α))
  (s : finset α) :
  (truncated_sup (𝒜 ∪ ℬ) s).card + (truncated_sup (𝒜 ⊼ ℬ) s).card =
    (truncated_sup 𝒜 s).card + (truncated_sup ℬ s).card :=
begin
  by_cases h𝒜 : s ∈ lower_closure (𝒜 : set $ finset α);
    by_cases hℬ : s ∈ lower_closure (ℬ : set $ finset α),
  { rw [truncated_sup_union h𝒜 hℬ, truncated_sup_infs h𝒜 hℬ],
    exact card_union_add_card_inter _ _ },
  { rw [truncated_sup_union_left h𝒜 hℬ, truncated_sup_of_not_mem hℬ,
      truncated_sup_infs_of_not_mem (λ h, hℬ h.2)] },
  { rw [truncated_sup_union_right h𝒜 hℬ, truncated_sup_of_not_mem h𝒜,
      truncated_sup_infs_of_not_mem (λ h, h𝒜 h.1), add_comm] },
  { rw [truncated_sup_of_not_mem h𝒜, truncated_sup_of_not_mem hℬ,
      truncated_sup_union_of_not_mem h𝒜 hℬ, truncated_sup_infs_of_not_mem (λ h, h𝒜 h.1)] }
end

end finset
