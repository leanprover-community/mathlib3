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

This file proves the Ahlswede-Zhang identity, which is a nontrivial relation between the size of the
"truncated unions"  of a set family. It sharpens the Lubell-Yamamoto-Meshalkin inequality
`finset.sum_card_slice_div_choose_le_one`, by making explicit the correction term.

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

namespace finset
variables {α β : Type*} [add_comm_monoid β]
open_locale big_operators

/-- A sum over `powerset_len` which only depends on the size of the sets is constant. -/
lemma sum_powerset_len (n : ℕ) (s : finset α) (f : ℕ → β) :
  ∑ t in powerset_len n s, f t.card = s.card.choose n • f n :=
by rw [sum_eq_card_nsmul, card_powerset_len]; rintro a ha; rw (mem_powerset_len.1 ha).2

end finset

namespace finset
variables {α : Type*} [fintype α] [decidable_eq α] {s t : finset α}

attribute [protected] finset.inf_eq_top_iff

@[simp] lemma inter_eq_univ : s ∩ t = univ ↔ s = univ ∧ t = univ := inf_eq_top_iff
--TODO: Rename `finset.union_eq_empty_iff` → `finset.union_eq_empty`

@[simp] lemma compl_subset_compl_iff : sᶜ ⊆ tᶜ ↔ t ⊆ s := @compl_le_compl_iff_le (finset α) _ _ _

lemma filter_subset_univ (s : finset α) : filter (λ t, t ⊆ s) univ = powerset s :=
by { ext, simp }

end finset

section
variables {m n : ℕ}
open finset fintype nat
open_locale big_operators

lemma binomial_sum_eq (h : n < m) :
  ∑ i in range (n + 1), (n.choose i * (m - n) / ((m - i) * m.choose i) : ℚ) = 1 :=
begin
  set f : ℕ → ℚ := λ i, n.choose i * (m.choose i)⁻¹ with hf,
  suffices : ∀ i ∈ range (n + 1),
    f i - f (i + 1) = n.choose i * (m - n) / ((m - i) * m.choose i),
  { rw [←sum_congr rfl this, sum_range_sub', hf],
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

variables (α : Type*) [fintype α] [nonempty α]

lemma fintype.sum_div_mul_card_choose_card :
  ∑ s : finset α, (card α / ((card α - s.card) * (card α).choose s.card) : ℚ) =
    card α * ∑ k in range (card α), k⁻¹ + 1 :=
begin
  rw [←powerset_univ, powerset_card_disj_Union, sum_disj_Union],
  have : ∀ {x : ℕ} (s ∈ powerset_len x (univ : finset α)),
    (card α / ((card α - (finset.card s)) * ((card α).choose (finset.card s))) : ℚ) =
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

end

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

@[simp] lemma truncated_sup_singleton (b a : α) : truncated_sup {b} a = if a ≤ b then b else ⊤ :=
by simp [truncated_sup]; split_ifs; simp [*]

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

@[simp] lemma truncated_inf_singleton (b a : α) :
  truncated_inf {b} a = if h : b ≤ a then b else ⊥ :=
by simp [truncated_inf]; split_ifs; simp [*]

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

lemma card_truncated_inf_union_add_card_truncated_inf_sups (𝒜 ℬ : finset (finset α))
  (s : finset α) :
  (truncated_inf (𝒜 ∪ ℬ) s).card + (truncated_inf (𝒜 ⊻ ℬ) s).card =
    (truncated_inf 𝒜 s).card + (truncated_inf ℬ s).card :=
begin
  by_cases h𝒜 : s ∈ upper_closure (𝒜 : set $ finset α);
    by_cases hℬ : s ∈ upper_closure (ℬ : set $ finset α),
  { rw [truncated_inf_union h𝒜 hℬ, truncated_inf_sups h𝒜 hℬ],
    exact card_inter_add_card_union _ _ },
  { rw [truncated_inf_union_left h𝒜 hℬ, truncated_inf_of_not_mem hℬ,
      truncated_inf_sups_of_not_mem (λ h, hℬ h.2)] },
  { rw [truncated_inf_union_right h𝒜 hℬ, truncated_inf_of_not_mem h𝒜,
      truncated_inf_sups_of_not_mem (λ h, h𝒜 h.1), add_comm] },
  { rw [truncated_inf_of_not_mem h𝒜, truncated_inf_of_not_mem hℬ,
      truncated_inf_union_of_not_mem h𝒜 hℬ, truncated_inf_sups_of_not_mem (λ h, h𝒜 h.1)] }
end

end finset

open finset (hiding card) fintype nat
open_locale big_operators

namespace ahlswede_zhang
variables {α : Type*} [fintype α] [decidable_eq α] {𝒜 ℬ : finset (finset α)} {s : finset α}

def inf_sum (𝒜 : finset (finset α)) : ℚ :=
∑ s, (truncated_inf 𝒜 s).card / (s.card * (card α).choose s.card)

def sup_sum (𝒜 : finset (finset α)) : ℚ :=
∑ s, (truncated_sup 𝒜 s).card / ((card α - s.card) * (card α).choose s.card)

lemma sup_sum_union_add_sup_sum_infs (𝒜 ℬ : finset (finset α)) :
  sup_sum (𝒜 ∪ ℬ) + sup_sum (𝒜 ⊼ ℬ) = sup_sum 𝒜 + sup_sum ℬ :=
begin
  unfold sup_sum,
  rw [←sum_add_distrib, ←sum_add_distrib, sum_congr rfl (λ s _, _)],
  simp_rw [div_add_div_same, ←nat.cast_add, card_truncated_sup_union_add_card_truncated_sup_infs],
end

lemma inf_sum_union_add_inf_sum_sups (𝒜 ℬ : finset (finset α)) :
  inf_sum (𝒜 ∪ ℬ) + inf_sum (𝒜 ⊻ ℬ) = inf_sum 𝒜 + inf_sum ℬ :=
begin
  unfold inf_sum,
  rw [←sum_add_distrib, ←sum_add_distrib, sum_congr rfl (λ s _, _)],
  simp_rw [div_add_div_same, ←nat.cast_add, card_truncated_inf_union_add_card_truncated_inf_sups],
end

variables [nonempty α]

@[simp] lemma sup_sum_singleton (hs : s ≠ univ) :
  sup_sum ({s} : finset (finset α)) = card α * ∑ k in range (card α), k⁻¹ :=
begin
  have : ∀ t : finset α,
    (card α - (truncated_sup {s} t).card : ℚ) / ((card α - t.card) * (card α).choose t.card)
      = ite (t ⊆ s) ((card α - s.card) / ((card α - t.card) * (card α).choose t.card)) 0,
  { rintro t,
    rw truncated_sup_singleton,
    split_ifs; simp [card_univ] },
  simp_rw [←sub_eq_of_eq_add (fintype.sum_div_mul_card_choose_card α), eq_sub_iff_add_eq,
    ←eq_sub_iff_add_eq', sup_sum, ←sum_sub_distrib, ←sub_div],
  rw [sum_congr rfl (λ t _, this t), sum_ite, sum_const_zero, add_zero, filter_subset_univ,
    sum_powerset, ←binomial_sum_eq ((card_lt_iff_ne_univ _).2 hs), eq_comm],
  refine sum_congr rfl (λ x hx, _),
  rw [mul_assoc (nat.choose _ _ : ℚ), mul_assoc, ←div_eq_mul_inv, ←div_eq_mul_inv, div_div,
    ←nsmul_eq_mul],
  exact sum_powerset_len _ _ (λ n, (card α - s.card : ℚ) / ((card α - n) * (card α).choose n)),
end

/-- The **Ahlswede-Zhang Identity**. -/
lemma inf_sum_compls_add_sup_sum (𝒜 : finset (finset α)) :
  inf_sum (𝒜.map ⟨compl, compl_injective⟩) + sup_sum 𝒜 = card α * ∑ k in range (card α), k⁻¹ + 1 :=
begin
  unfold inf_sum sup_sum,
  rw [←@map_univ_of_surjective (finset α) _ _ _ ⟨compl, compl_injective⟩ compl_surjective, sum_map],
  simp only [function.embedding.coe_fn_mk, univ_map_embedding, ←compl_truncated_sup,
    ←sum_add_distrib, card_compl, cast_sub (card_le_univ _), choose_symm (card_le_univ _),
    div_add_div_same, sub_add_cancel, fintype.sum_div_mul_card_choose_card],
end

lemma sup_sum_of_not_univ_mem (h𝒜₁ : 𝒜.nonempty) (h𝒜₂ : univ ∉ 𝒜) :
  sup_sum 𝒜 = card α * ∑ k in range (card α), k⁻¹ :=
begin
  set m := 𝒜.card with hm,
  clear_value m,
  induction m using nat.strong_induction_on with m ih generalizing 𝒜,
  dsimp at ih,
  replace ih := λ 𝒜 h𝒜 h𝒜₁ h𝒜₂, @ih _ h𝒜 𝒜 h𝒜₁ h𝒜₂ rfl,
  obtain ⟨a, rfl⟩ | h𝒜₃ := h𝒜₁.exists_eq_singleton_or_nontrivial,
  { refine sup_sum_singleton _,
    simpa [eq_comm] using h𝒜₂ },
  cases m,
  { cases h𝒜₁.card_pos.ne hm },
  obtain ⟨s, 𝒜, hs, rfl, rfl⟩ := card_eq_succ.1 hm.symm,
  have h𝒜 : 𝒜.nonempty := nonempty_iff_ne_empty.2 (by { rintro rfl, simpa using h𝒜₃ }),
  rw [insert_eq, eq_sub_of_add_eq (sup_sum_union_add_sup_sum_infs _ _), singleton_infs,
    sup_sum_singleton (ne_of_mem_of_not_mem (mem_insert_self _ _) h𝒜₂), ih, ih],
  simp,
  { exact card_image_le.trans_lt (lt_add_one _) },
  { exact h𝒜.image _ },
  { simpa using λ _, ne_of_mem_of_not_mem (mem_insert_self _ _) h𝒜₂ },
  { exact lt_add_one _ },
  { exact h𝒜 },
  { exact λ h, h𝒜₂ (mem_insert_of_mem h) }
end

end ahlswede_zhang
