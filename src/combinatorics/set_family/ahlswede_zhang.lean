/-
Copyright (c) 2023 Yaël Dillies, Vladimir Ivanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Ivanov
-/
import data.finset.sups

/-!
# The Ahlswede-Zhang identity

This file proves the Ahlswede-Zhang identity, which is a nontrivial relation between the size of the
"truncated unions"  of a set family. It sharpens the Lubell-Yamamoto-Meshalkin inequality
`finset.sum_card_slice_div_choose_le_one`, by expliciting the correction term.

For a set family `𝒜`, the Ahlswede-Zhang identity states that the sum of
`|⋂ B ∈ 𝒜, B ⊆ A, B|/(|A| * n.choose |A|)` is exactly `1`.

## Main declarations

* `finset.truncated_sup`: `s.truncated_sup a` is the supremum of all `b ≤ a` in `𝒜` if there are
  some, or `⊤` if there are none.
* `finset.truncated_inf` `s.truncated_inf a` is the infimum of all `b ≥ a` in `𝒜` if there are
  some, or `⊥` if there are none.

## References

* [R. Ahlswede, Z. Zhang, *An identity in combinatorial extremal theory*](https://doi.org/10.1016/0001-8708(90)90023-G)
* [D. T. Tru, *An AZ-style identity and Bollobás deficiency*](https://doi.org/10.1016/j.jcta.2007.03.005)
-/

open_locale finset_family

namespace finset
variables {α β : Type*}

/-! ### Truncated supremum, truncated infimum -/

section semilattice_sup
variables [semilattice_sup α] [order_top α] [@decidable_rel α (≤)]
  [semilattice_sup β] [bounded_order β] [@decidable_rel β (≤)] {s t : finset α} {a b : α}

private lemma sup_aux : a ∈ lower_closure (s : set α) → (s.filter $ λ b, a ≤ b).nonempty :=
λ ⟨b, hb, hab⟩, ⟨b, mem_filter.2 ⟨hb, hab⟩⟩

/-- The infimum of the elements of `s` less than `a` if there are some, otherwise `⊤`. -/
def truncated_sup (s : finset α) (a : α) : α :=
if h : a ∈ lower_closure (s : set α) then (s.filter $ λ b, a ≤ b).sup' (sup_aux h) id else ⊤

lemma truncated_sup_of_mem (h : a ∈ lower_closure (s : set α)) :
  truncated_sup s a = (s.filter $ λ b, a ≤ b).sup' (sup_aux h) id := dif_pos h

lemma truncated_sup_of_not_mem (h : a ∉ lower_closure (s : set α)) : truncated_sup s a = ⊤ :=
dif_neg h

@[simp] lemma truncated_sup_empty (a : α) : truncated_sup ∅ a = ⊤ :=
truncated_sup_of_not_mem $ by simp

lemma le_truncated_sup : a ≤ truncated_sup s a :=
begin
  rw truncated_sup,
  split_ifs,
  { obtain ⟨ℬ, hb, h⟩ := h,
    exact h.trans (le_sup' _ $ mem_filter.2 ⟨hb, h⟩) },
  { exact le_top }
end

lemma map_truncated_sup (e : α ≃o β) (s : finset α) (a : α) :
  e (truncated_sup s a) = truncated_sup (s.map e.to_equiv.to_embedding) (e a) :=
begin
  have : e a ∈ lower_closure (s.map e.to_equiv.to_embedding : set β)
    ↔ a ∈ lower_closure (s : set α),
  { simp },
  simp_rw [truncated_sup, apply_dite e, map_finset_sup', map_top, this],
  congr' with h,
  simp only [filter_map, function.comp, equiv.coe_to_embedding, rel_iso.coe_fn_to_equiv,
    order_iso.le_iff_le, id.def],
  rw sup'_map, -- TODO: Why can't `simp` use `finset.sup'_map`?
  simp only [equiv.coe_to_embedding, rel_iso.coe_fn_to_equiv],
end

variables [decidable_eq α]

private lemma lower_aux :
  a ∈ lower_closure (↑(s ∪ t) : set α) ↔
    a ∈ lower_closure (s : set α) ∨ a ∈ lower_closure (t : set α) :=
by rw [coe_union, lower_closure_union, lower_set.mem_sup_iff]

lemma truncated_sup_union (hs : a ∈ lower_closure (s : set α))
  (ht : a ∈ lower_closure (t : set α)) :
  truncated_sup (s ∪ t) a = truncated_sup s a ⊔ truncated_sup t a :=
by simpa only [truncated_sup_of_mem, hs, ht, lower_aux.2 (or.inl hs), filter_union]
  using sup'_union _ _ _

lemma truncated_sup_union_left (hs : a ∈ lower_closure (s : set α))
  (ht : a ∉ lower_closure (t : set α)) :
  truncated_sup (s ∪ t) a = truncated_sup s a :=
begin
  simp only [mem_lower_closure, mem_coe, exists_prop, not_exists, not_and] at ht,
  simp only [truncated_sup_of_mem, hs, filter_union, filter_false_of_mem ht, union_empty,
    lower_aux.2 (or.inl hs), ht],
end

lemma truncated_sup_union_right (hs : a ∉ lower_closure (s : set α))
  (ht : a ∈ lower_closure (t : set α)) :
  truncated_sup (s ∪ t) a = truncated_sup t a :=
by rw [union_comm, truncated_sup_union_left ht hs]

lemma truncated_sup_union_of_not_mem (hs : a ∉ lower_closure (s : set α))
  (ht : a ∉ lower_closure (t : set α)) :
  truncated_sup (s ∪ t) a = ⊤ :=
truncated_sup_of_not_mem $ λ h, (lower_aux.1 h).elim hs ht

end semilattice_sup

section semilattice_inf
variables [semilattice_inf α] [bounded_order α] [@decidable_rel α (≤)]
  [semilattice_inf β] [bounded_order β] [@decidable_rel β (≤)] {s t : finset α} {a : α}

private lemma inf_aux : a ∈ upper_closure (s : set α) → (s.filter $ λ b, b ≤ a).nonempty :=
λ ⟨b, hb, hab⟩, ⟨b, mem_filter.2 ⟨hb, hab⟩⟩

/-- The infimum of the elements of `s` less than `a` if there are some, otherwise `⊥`. -/
def truncated_inf (s : finset α) (a : α) : α :=
if h : a ∈ upper_closure (s : set α) then (s.filter $ λ b, b ≤ a).inf' (inf_aux h) id else ⊥

lemma truncated_inf_of_mem (h : a ∈ upper_closure (s : set α)) :
  truncated_inf s a = (s.filter $ λ b, b ≤ a).inf' (inf_aux h) id := dif_pos h

lemma truncated_inf_of_not_mem (h : a ∉ upper_closure (s : set α)) : truncated_inf s a = ⊥ :=
dif_neg h

lemma truncated_inf_le (s : finset α) (a : α) : truncated_inf s a ≤ a :=
begin
  unfold truncated_inf,
  split_ifs,
  { obtain ⟨ℬ, hb, h⟩ := h,
    exact (inf'_le _ $ mem_filter.2 ⟨hb, h⟩).trans h },
  { exact bot_le }
end

@[simp] lemma truncated_inf_empty (a : α) : truncated_inf ∅ a = ⊥ :=
truncated_inf_of_not_mem $ by simp

lemma map_truncated_inf (e : α ≃o β) (s : finset α) (a : α) :
  e (truncated_inf s a) = truncated_inf (s.map e.to_equiv.to_embedding) (e a) :=
begin
  have : e a ∈ upper_closure (s.map e.to_equiv.to_embedding : set β)
    ↔ a ∈ upper_closure (s : set α),
  { simp },
  simp_rw [truncated_inf, apply_dite e, map_finset_inf', map_bot, this],
  congr' with h,
  simp only [filter_map, function.comp, equiv.coe_to_embedding, rel_iso.coe_fn_to_equiv,
    order_iso.le_iff_le, id.def],
  rw inf'_map, -- TODO: Why can't `simp` use `finset.inf'_map`?
  simp only [equiv.coe_to_embedding, rel_iso.coe_fn_to_equiv],
end

variables [decidable_eq α]

private lemma upper_aux :
  a ∈ upper_closure (↑(s ∪ t) : set α) ↔
    a ∈ upper_closure (s : set α) ∨ a ∈ upper_closure (t : set α) :=
by rw [coe_union, upper_closure_union, upper_set.mem_inf_iff]

lemma truncated_inf_union (hs : a ∈ upper_closure (s : set α))
  (ht : a ∈ upper_closure (t : set α)) :
  truncated_inf (s ∪ t) a = truncated_inf s a ⊓ truncated_inf t a :=
by simpa only [truncated_inf_of_mem, hs, ht, upper_aux.2 (or.inl hs), filter_union]
  using inf'_union _ _ _

lemma truncated_inf_union_left (hs : a ∈ upper_closure (s : set α))
  (ht : a ∉ upper_closure (t : set α)) :
  truncated_inf (s ∪ t) a = truncated_inf s a :=
begin
  simp only [mem_upper_closure, mem_coe, exists_prop, not_exists, not_and] at ht,
  simp only [truncated_inf_of_mem, hs, filter_union, filter_false_of_mem ht, union_empty,
    upper_aux.2 (or.inl hs), ht],
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

private lemma infs_aux
 : a ∈ lower_closure (↑(s ⊼ t) : set α) ↔ a ∈ lower_closure (s : set α) ⊓ lower_closure t :=
by rw [coe_infs, lower_closure_infs, lower_set.mem_inf_iff]

private lemma sups_aux :
  a ∈ upper_closure (↑(s ⊻ t) : set α) ↔ a ∈ upper_closure (s : set α) ⊔ upper_closure t :=
by rw [coe_sups, upper_closure_sups, upper_set.mem_sup_iff]

lemma truncated_sup_infs (hs : a ∈ lower_closure (s : set α)) (ht : a ∈ lower_closure (t : set α)) :
  truncated_sup (s ⊼ t) a = truncated_sup s a ⊓ truncated_sup t a :=
begin
  simp only [truncated_sup_of_mem, hs, ht, infs_aux.2 ⟨hs, ht⟩, sup'_inf_sup', filter_infs_ge],
  simp_rw ←image_inf_product,
  rw sup'_image,
  refl,
end

lemma truncated_inf_sups (hs : a ∈ upper_closure (s : set α)) (ht : a ∈ upper_closure (t : set α)) :
  truncated_inf (s ⊻ t) a = truncated_inf s a ⊔ truncated_inf t a :=
begin
  simp only [truncated_inf_of_mem, hs, ht, sups_aux.2 ⟨hs, ht⟩, inf'_sup_inf', filter_sups_le],
  simp_rw ←image_sup_product,
  rw inf'_image,
  refl,
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

variables [decidable_eq α] [fintype α]

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
