/-
Copyright (c) 2023 Yaël Dillies, Vladimir Ivanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Ivanov
-/
import algebra.big_operators.ring
import data.finset.sups
import data.fintype.powerset
import order.hom.lattice
import tactic.field_simp
import tactic.ring

/-!
# The Ahlswede-Zhang identity

This file proves the Ahlswede-Zhang identity, which is a nontrivial relation between

## Main declarations

* `finset.truncated_sup`
* `finset.truncated_inf`
-/

namespace finset
variables {ι ι' α β γ δ : Type*}

-- TODO: Rename `finset.image_filter` → `finset.filter_image`
-- TODO: Dedup `finset.sup_image`, `finset.sup_finset_image`

open function

section
variables [distrib_lattice α] [order_bot α] {f : ι → α} {g : ι' → α} {s : finset ι} {t : finset ι'}

lemma sup_inf_sup : s.sup f ⊓ t.sup g = (s ×ˢ t).sup (λ i, f i.1 ⊓ g i.2) :=
by simp_rw [finset.sup_inf_distrib_right, finset.sup_inf_distrib_left, sup_product_left]

end

section
variables [distrib_lattice α] [order_top α] {f : ι → α} {g : ι' → α} {s : finset ι} {t : finset ι'}

lemma inf_sup_inf : s.inf f ⊔ t.inf g = (s ×ˢ t).inf (λ i, f i.1 ⊔ g i.2) :=
by simp_rw [finset.inf_sup_distrib_right, finset.inf_sup_distrib_left, inf_product_left]

end

section
variables [semilattice_sup δ] [order_bot δ] [decidable_eq γ]

lemma sup_image₂ (s : finset α) (t : finset β) (f : α → β → γ) (g : γ → δ) :
  (image₂ f s t).sup g = (s ×ˢ t).sup (g ∘ uncurry f) :=
by rw [←image_uncurry_product, sup_image]

end

section
variables [semilattice_inf δ] [order_top δ] [decidable_eq γ]

lemma inf_image₂ (s : finset α) (t : finset β) (f : α → β → γ) (g : γ → δ) :
  (image₂ f s t).inf g = (s ×ˢ t).inf (g ∘ uncurry f) :=
by rw [←image_uncurry_product, inf_image]

end

section fintype
variables [fintype α] [decidable_eq α] {s t : finset α}

attribute [protected] finset.inf_eq_top_iff

@[simp] lemma inter_eq_univ : s ∩ t = univ ↔ s = univ ∧ t = univ := inf_eq_top_iff
--TODO: Rename `finset.union_eq_empty_iff` → `finset.union_eq_empty`

@[simp] lemma compl_subset_compl_iff : sᶜ ⊆ tᶜ ↔ t ⊆ s := @compl_le_compl_iff_le (finset α) _ _ _

lemma filter_subset_univ (s : finset α) : filter (λ t, t ⊆ s) univ = powerset s :=
by { ext, simp }

end fintype

section boolean_algebra
variables [boolean_algebra α]

@[simp] protected lemma compl_sup (s : finset ι) (f : ι → α) : (s.sup f)ᶜ = s.inf (compl ∘ f) :=
map_finset_sup (order_iso.compl α) _ _

@[simp] protected lemma compl_inf (s : finset ι) (f : ι → α) : (s.inf f)ᶜ = s.sup (compl ∘ f) :=
map_finset_inf (order_iso.compl α) _ _

end boolean_algebra

section preorder
variables [preorder α] {s t : set α} {a : α}

instance decidable_pred_mem_upper_closure (s : finset α) [@decidable_rel α (≤)] :
  decidable_pred (∈ upper_closure (s : set α)) :=
λ _, finset.decidable_dexists_finset

instance decidable_pred_mem_lower_closure (s : finset α) [@decidable_rel α (≤)] :
  decidable_pred (∈ lower_closure (s : set α)) :=
λ _, finset.decidable_dexists_finset

end preorder

open_locale finset_family

section semilattice_sup
variables [decidable_eq α] [semilattice_sup α] [@decidable_rel α (≤)]

lemma filter_sups_le (s t : finset α) (a : α) :
  (s ⊻ t).filter (λ b, b ≤ a) = s.filter (λ b, b ≤ a) ⊻ t.filter (λ b, b ≤ a) :=
begin
  ext b,
  simp only [mem_filter, mem_sups],
  split,
  { rintro ⟨⟨b, hb, c, hc, rfl⟩, ha⟩,
    rw sup_le_iff at ha,
    exact ⟨_, ⟨hb, ha.1⟩, _, ⟨hc, ha.2⟩, rfl⟩ },
  { rintro ⟨b, hb, c, hc, _, rfl⟩,
    exact ⟨⟨_, hb.1, _, hc.1, rfl⟩, sup_le hb.2 hc.2⟩ }
end

end semilattice_sup

section semilattice_inf
variables [decidable_eq α] [semilattice_inf α] [@decidable_rel α (≤)]

lemma filter_infs_ge (s t : finset α) (a : α) :
  (s ⊼ t).filter (λ b, a ≤ b) = s.filter (λ b, a ≤ b) ⊼ t.filter (λ b, a ≤ b) :=
begin
  ext b,
  simp only [mem_filter, mem_infs],
  split,
  { rintro ⟨⟨b, hb, c, hc, rfl⟩, ha⟩,
    rw le_inf_iff at ha,
    exact ⟨_, ⟨hb, ha.1⟩, _, ⟨hc, ha.2⟩, rfl⟩ },
  { rintro ⟨b, hb, c, hc, _, rfl⟩,
    exact ⟨⟨_, hb.1, _, hc.1, rfl⟩, le_inf hb.2 hc.2⟩ }
end

end semilattice_inf
end finset

open_locale finset_family

namespace finset
variables {α : Type*}

/-! ### Truncated supremum, truncated infimum -/

section semilattice_sup
variables [semilattice_sup α] [bounded_order α] [@decidable_rel α (≤)] {s t : finset α} {a b : α}

/-- The infimum of the elements of `s` less than `a` if there are some, otherwise `⊥`. -/
def truncated_sup (s : finset α) (a : α) : α :=
if a ∈ lower_closure (s : set α) then (s.filter $ λ b, a ≤ b).sup id else ⊤

lemma truncated_sup_of_mem (h : a ∈ lower_closure (s : set α)) :
  truncated_sup s a = (s.filter $ λ b, a ≤ b).sup id :=
if_pos h

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
variables [semilattice_inf α] [bounded_order α] [@decidable_rel α (≤)] {s t : finset α} {a : α}

/-- The infimum of the elements of `s` less than `a` if there are some, otherwise `⊥`. -/
def truncated_inf (s : finset α) (a : α) : α :=
if a ∈ upper_closure (s : set α) then (s.filter $ λ b, b ≤ a).inf id else ⊥

lemma truncated_inf_of_mem (h : a ∈ upper_closure (s : set α)) :
  truncated_inf s a = (s.filter $ λ b, b ≤ a).inf id :=
if_pos h

lemma truncated_inf_of_not_mem (h : a ∉ upper_closure (s : set α)) : truncated_inf s a = ⊥ :=
if_neg h

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
begin
  unfold truncated_sup,
  split_ifs,
  { rw truncated_inf_of_mem,
    simp [filter_map, function.comp],
    simpa using h },
  { rw [compl_top, truncated_inf_of_not_mem],
    simpa using h }
end

@[simp] lemma compl_truncated_inf (s : finset α) (a : α) :
  (truncated_inf s a)ᶜ = truncated_sup (s.map ⟨compl, compl_injective⟩) aᶜ :=
begin
  unfold truncated_inf,
  split_ifs,
  { rw truncated_sup_of_mem,
    simp [filter_map, function.comp],
    simpa using h },
  { rw [compl_bot, truncated_sup_of_not_mem],
    simpa using h }
end

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

open finset (hiding card) fintype nat
open_locale big_operators

variables {α : Type*} [fintype α] {𝒜 ℬ : finset (finset α)} {s : finset α}

lemma sum_div_sub_card_mul_choose_card_eq_mul_sum_range_inv_add_one [nonempty α] :
  ∑ i : finset α, (card α / ((card α - i.card) * (card α).choose i.card) : ℚ) =
    card α * ∑ k in range (card α), k⁻¹ + 1 :=
begin
  rw [←powerset_univ, powerset_card_disj_Union, sum_disj_Union],
  have : ∀ {x : ℕ} (i ∈ powerset_len x (univ : finset α)),
    (card α / ((card α - (finset.card i)) * ((card α).choose (finset.card i))) : ℚ) =
    card α / ((card α - x) * ((card α).choose x)),
  { intros,
    rw mem_powerset_len_univ_iff.mp H },
  simp_rw [sum_congr rfl this, sum_const, card_powerset_len, card_univ],
  simp,
  simp_rw [mul_div, mul_comm, ←mul_div],
  rw [←mul_sum, ←mul_inv_cancel (cast_ne_zero.mpr card_ne_zero : (card α : ℚ) ≠ 0), ←mul_add,
      add_comm _ ((card α)⁻¹ : ℚ),
      ←(@sum_insert _ _ _ _ (λ x : ℕ, (x⁻¹ : ℚ)) _ _ not_mem_range_self), ←range_succ],
  have : ∀ x ∈ range (card α + 1),
    (((card α).choose x) / (((card α).choose x) * (card α - x)) : ℚ) = (card α - x)⁻¹,
  { intros,
    rw div_mul_right,
    { simp },
    { exact cast_ne_zero.mpr (ne_of_gt (choose_pos (mem_range_succ_iff.mp H))) } },
  simp only [sum_congr rfl this, mul_eq_mul_left_iff, cast_eq_zero],
  left,
  exact sum_bij (λ n _, card α - n)
    (λ a ha, mem_range_succ_iff.mpr tsub_le_self)
    (λ a ha, by rw cast_sub (mem_range_succ_iff.mp ha))
    (λ a₁ a₂ ha₁ ha₂ heq,
      (tsub_right_inj (mem_range_succ_iff.mp ha₁) (mem_range_succ_iff.mp ha₂)).mp heq)
    (λ b hb, ⟨card α - b, mem_range_succ_iff.mpr tsub_le_self,
      (tsub_tsub_cancel_of_le (mem_range_succ_iff.mp hb)).symm⟩),
end

variables [decidable_eq α]

def sum_truncated_inf_div_card_mul_choose (𝒜 : finset (finset α)) : ℚ :=
∑ s, (truncated_inf 𝒜 s).card / (s.card * (card α).choose s.card)

def sum_truncated_sup_div_sub_card_mul_choose (𝒜 : finset (finset α)) : ℚ :=
∑ s, (truncated_sup 𝒜 s).card / ((card α - s.card) * (card α).choose s.card)

lemma sum_truncated_inf_div_card_mul_choose_union_eq (𝒜 ℬ : finset (finset α)) :
  sum_truncated_sup_div_sub_card_mul_choose (𝒜 ∪ ℬ) =
  sum_truncated_sup_div_sub_card_mul_choose 𝒜 + sum_truncated_sup_div_sub_card_mul_choose ℬ -
  sum_truncated_sup_div_sub_card_mul_choose (𝒜 ⊼ ℬ) :=
begin
  refine eq_sub_of_add_eq _,
  dunfold sum_truncated_sup_div_sub_card_mul_choose,
  rw [←sum_add_distrib, ←sum_add_distrib, sum_congr rfl (λ s _, _)],
  rw [div_add_div_same, div_add_div_same, ←nat.cast_add, ←nat.cast_add,
    card_truncated_sup_union_add_card_truncated_sup_infs],
end

lemma ahlswede_zhang [nonempty α] (𝒜 : finset ( finset α)) :
  sum_truncated_inf_div_card_mul_choose (𝒜.map ⟨compl, compl_injective⟩)
  + sum_truncated_sup_div_sub_card_mul_choose 𝒜 = card α * ∑ k in range (card α), k⁻¹ + 1 :=
begin
  unfold sum_truncated_inf_div_card_mul_choose sum_truncated_sup_div_sub_card_mul_choose,
  rw [←@map_univ_of_surjective (finset α) _ _ _ ⟨compl, compl_injective⟩ compl_surjective, sum_map],
  simp only [function.embedding.coe_fn_mk, univ_map_embedding],
  simp_rw [←compl_truncated_sup, ←sum_add_distrib, card_compl, cast_sub (card_le_univ _),
    choose_symm (card_le_univ _), div_add_div_same, sub_add_cancel],
  exact sum_div_sub_card_mul_choose_card_eq_mul_sum_range_inv_add_one,
end

lemma binomial_sum_eq {n m : ℕ} (h : n < m) :
  ∑ i in range (n+1), ((n.choose i) * (n - m) * (m - i)⁻¹ * (m.choose i)⁻¹ : ℚ) = -1 :=
begin
  set f : ℕ → ℚ := λ i, n.choose i * (m.choose i)⁻¹ with hf,
  suffices : ∀ i ∈ range (n + 1),
    f (i + 1) - f i = n.choose i * (n - m) * (m - i)⁻¹ * (m.choose i)⁻¹,
  { rw [←sum_congr rfl this, sum_range_sub, hf],
    simp [nat.choose_self, nat.choose_zero_right, nat.choose_eq_zero_of_lt h] },
  intros i h₁,
  rw mem_range at h₁,
  have h₁ := nat.le_of_lt_succ h₁,
  have h₂ := h₁.trans_lt h,
  have h₃ := h₂.le,
  have hi₄ : (i + 1 : ℚ) ≠ 0,
  { have := (@nat.cast_ne_zero ℚ _ _ _).mpr (nat.succ_ne_zero i),
    push_cast at this,
    exact this },
  have := congr_arg (coe : ℕ → ℚ) (nat.choose_succ_right_eq m i),
  push_cast at this,
  dsimp [f],
  rw (eq_mul_inv_iff_mul_eq₀ hi₄).mpr this,
  have := congr_arg (coe : ℕ → ℚ) (nat.choose_succ_right_eq n i),
  push_cast at this,
  rw (eq_mul_inv_iff_mul_eq₀ hi₄).mpr this,
  have : (m - i : ℚ) ≠ 0 := sub_ne_zero_of_ne (nat.cast_lt.mpr h₂).ne',
  have : (n.choose i : ℚ) ≠ 0 := nat.cast_ne_zero.2 (nat.choose_pos h₁).ne',
  have : (m.choose i : ℚ) ≠ 0 := nat.cast_ne_zero.2 (nat.choose_pos h₂.le).ne',
  field_simp,
  ring,
end

lemma sum_truncated_sup_div_sub_card_mul_choose_singleton_eq_mul_sum_range_inv [nonempty α]
  (hs : s ≠ univ) :
  sum_truncated_sup_div_sub_card_mul_choose ({s} : finset (finset α)) =
    card α * ∑ k in range (card α), k⁻¹ :=
begin
  rw ←sub_eq_of_eq_add sum_div_sub_card_mul_choose_card_eq_mul_sum_range_inv_add_one,
  dunfold sum_truncated_sup_div_sub_card_mul_choose,
  simp only [truncated_sup, filter_singleton, coe_singleton, lower_closure_singleton,
    lower_set.mem_Iic_iff, le_eq_subset, top_eq_univ],
  rw sub_eq_add_neg,
  refine eq_add_of_sub_eq' _,
  simp_rw [←sum_sub_distrib, div_sub_div_same],
  rw [←sum_filter_add_sum_filter_not _ (λ x, x ⊆ s), add_comm, sum_congr rfl],
  swap,
  { intros x hx,
    rw if_neg (mem_filter.mp hx).2 },
  simp_rw [top_eq_univ, ←finset.card_univ, sub_self, zero_div, sum_const_zero, zero_add],
  rw [filter_subset_univ, sum_congr rfl],
  swap,
  { intros x hx,
    simp [if_pos (mem_powerset.mp hx)] },
  rw [powerset_card_disj_Union, sum_disj_Union, ←binomial_sum_eq ((card_lt_iff_ne_univ _).2 hs)],
  refine sum_congr rfl (λ x hx, (sum_congr rfl $ λ i hi, _).trans _),
  swap,
  { rw (mem_powerset_len.mp hi).2 },
  simp [sum_const, card_univ],
  field_simp,
  apply_instance, -- why do i need this?
end

theorem Γ_eq_Φ [nonempty α] (h𝒜₁ : 𝒜.nonempty) (h𝒜₂ : univ ∉ 𝒜) :
  sum_truncated_sup_div_sub_card_mul_choose 𝒜 = card α * ∑ k in range (card α), k⁻¹ :=
begin
  set m := 𝒜.card with hm,
  clear_value m,
  induction m using nat.strong_induction_on with m ih generalizing 𝒜,
  dsimp at ih,
  replace ih := λ 𝒜 h𝒜 h𝒜₁ h𝒜₂, @ih _ h𝒜 𝒜 h𝒜₁ h𝒜₂ rfl,
  obtain ⟨a, rfl⟩ | h𝒜₃ := h𝒜₁.exists_eq_singleton_or_nontrivial,
  { refine sum_truncated_sup_div_sub_card_mul_choose_singleton_eq_mul_sum_range_inv _,
    simpa [eq_comm] using h𝒜₂ },
  cases m,
  { cases h𝒜₁.card_pos.ne hm },
  obtain ⟨s, 𝒜, hs, rfl, rfl⟩ := card_eq_succ.1 hm.symm,
  have h𝒜 : 𝒜.nonempty := nonempty_iff_ne_empty.2 (by { rintro rfl, simpa using h𝒜₃ }),
  rw [insert_eq, sum_truncated_inf_div_card_mul_choose_union_eq, singleton_infs, ih, ih, ih],
  simp,
  { exact card_image_le.trans_lt (lt_add_one _) },
  { exact h𝒜.image _ },
  { simpa using λ _, ne_of_mem_of_not_mem (mem_insert_self _ _) h𝒜₂ },
  { exact lt_add_one _ },
  { exact h𝒜 },
  { exact λ h, h𝒜₂ (mem_insert_of_mem h) },
  { simpa only [nat.succ_eq_add_one, card_singleton, ←card_insert_of_not_mem hs,
      finset.one_lt_card] },
  { simp },
  { simpa [eq_comm] using ne_of_mem_of_not_mem (mem_insert_self _ _) h𝒜₂ }
end
