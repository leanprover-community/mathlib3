/-
Copyright (c) 2022 Bhavik Mehta, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
import algebra.big_operators.ring
import algebra.order.field.basic
import combinatorics.double_counting
import combinatorics.set_family.shadow
import data.rat.order

/-!
# Lubell-Yamamoto-Meshalkin inequality and Sperner's theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves the local LYM and LYM inequalities as well as Sperner's theorem.

## Main declarations

* `finset.card_div_choose_le_card_shadow_div_choose`: Local Lubell-Yamamoto-Meshalkin inequality.
  The shadow of a set `𝒜` in a layer takes a greater proportion of its layer than `𝒜` does.
* `finset.sum_card_slice_div_choose_le_one`: Lubell-Yamamoto-Meshalkin inequality. The sum of
  densities of `𝒜` in each layer is at most `1` for any antichain `𝒜`.
* `is_antichain.sperner`: Sperner's theorem. The size of any antichain in `finset α` is at most the
  size of the maximal layer of `finset α`. It is a corollary of `sum_card_slice_div_choose_le_one`.

## TODO

Prove upward local LYM.

Provide equality cases. Local LYM gives that the equality case of LYM and Sperner is precisely when
`𝒜` is a middle layer.

`falling` could be useful more generally in grade orders.

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, lym, slice, sperner, antichain
-/

open finset nat
open_locale big_operators finset_family

variables {𝕜 α : Type*} [linear_ordered_field 𝕜]

namespace finset

/-! ### Local LYM inequality -/

section local_lym
variables [decidable_eq α] [fintype α] {𝒜 : finset (finset α)} {r : ℕ}

/-- The downward **local LYM inequality**, with cancelled denominators. `𝒜` takes up less of `α^(r)`
(the finsets of card `r`) than `∂𝒜` takes up of `α^(r - 1)`. -/
lemma card_mul_le_card_shadow_mul (h𝒜 : (𝒜 : set (finset α)).sized r) :
  𝒜.card * r ≤ (∂𝒜).card * (fintype.card α - r + 1) :=
begin
  refine card_mul_le_card_mul' (⊆) (λ s hs, _) (λ s hs, _),
  { rw [←h𝒜 hs, ←card_image_of_inj_on s.erase_inj_on],
    refine card_le_of_subset _,
    simp_rw [image_subset_iff, mem_bipartite_below],
    exact λ a ha, ⟨erase_mem_shadow hs ha, erase_subset _ _⟩ },
  refine le_trans _ tsub_tsub_le_tsub_add,
  rw [←h𝒜.shadow hs, ←card_compl, ←card_image_of_inj_on (insert_inj_on' _)],
  refine card_le_of_subset (λ t ht, _),
  apply_instance,
  rw mem_bipartite_above at ht,
  have : ∅ ∉ 𝒜,
  { rw [←mem_coe, h𝒜.empty_mem_iff, coe_eq_singleton],
    rintro rfl,
    rwa shadow_singleton_empty at hs },
  obtain ⟨a, ha, rfl⟩ :=
    exists_eq_insert_iff.2 ⟨ht.2, by rw [(sized_shadow_iff this).1 h𝒜.shadow ht.1, h𝒜.shadow hs]⟩,
  exact mem_image_of_mem _ (mem_compl.2 ha),
end

/-- The downward **local LYM inequality**. `𝒜` takes up less of `α^(r)` (the finsets of card `r`)
than `∂𝒜` takes up of `α^(r - 1)`. -/
lemma card_div_choose_le_card_shadow_div_choose (hr : r ≠ 0) (h𝒜 : (𝒜 : set (finset α)).sized r) :
  (𝒜.card : 𝕜) / (fintype.card α).choose r ≤ (∂𝒜).card / (fintype.card α).choose (r - 1) :=
begin
  obtain hr' | hr' := lt_or_le (fintype.card α) r,
  { rw [choose_eq_zero_of_lt hr', cast_zero, div_zero],
    exact div_nonneg (cast_nonneg _) (cast_nonneg _) },
  replace h𝒜 := card_mul_le_card_shadow_mul h𝒜,
  rw div_le_div_iff; norm_cast,
  { cases r,
    { exact (hr rfl).elim },
    rw nat.succ_eq_add_one at *,
    rw [tsub_add_eq_add_tsub hr', add_tsub_add_eq_tsub_right] at h𝒜,
    apply le_of_mul_le_mul_right _ (pos_iff_ne_zero.2 hr),
    convert nat.mul_le_mul_right ((fintype.card α).choose r) h𝒜 using 1,
    { simp [mul_assoc, nat.choose_succ_right_eq],
      exact or.inl (mul_comm _ _) },
    { simp only [mul_assoc, choose_succ_right_eq, mul_eq_mul_left_iff],
      exact or.inl (mul_comm _ _) } },
  { exact nat.choose_pos hr' },
  { exact nat.choose_pos (r.pred_le.trans hr') }
end

end local_lym

/-! ### LYM inequality -/

section lym
section falling
variables [decidable_eq α] (k : ℕ) (𝒜 : finset (finset α))

/-- `falling k 𝒜` is all the finsets of cardinality `k` which are a subset of something in `𝒜`. -/
def falling : finset (finset α) := 𝒜.sup $ powerset_len k

variables {𝒜 k} {s : finset α}

lemma mem_falling : s ∈ falling k 𝒜 ↔ (∃ t ∈ 𝒜, s ⊆ t) ∧ s.card = k :=
by simp_rw [falling, mem_sup, mem_powerset_len, exists_and_distrib_right]

variables (𝒜 k)

lemma sized_falling : (falling k 𝒜 : set (finset α)).sized k := λ s hs, (mem_falling.1 hs).2

lemma slice_subset_falling : 𝒜 # k ⊆ falling k 𝒜 :=
λ s hs, mem_falling.2 $ (mem_slice.1 hs).imp_left $ λ h, ⟨s, h, subset.refl _⟩

lemma falling_zero_subset : falling 0 𝒜 ⊆ {∅} :=
subset_singleton_iff'.2 $ λ t ht, card_eq_zero.1 $ sized_falling _ _ ht

lemma slice_union_shadow_falling_succ : 𝒜 # k ∪ ∂ (falling (k + 1) 𝒜) = falling k 𝒜 :=
begin
  ext s,
  simp_rw [mem_union, mem_slice, mem_shadow_iff, exists_prop, mem_falling],
  split,
  { rintro (h | ⟨s, ⟨⟨t, ht, hst⟩, hs⟩, a, ha, rfl⟩),
    { exact ⟨⟨s, h.1, subset.refl _⟩, h.2⟩ },
    refine ⟨⟨t, ht, (erase_subset _ _).trans hst⟩, _⟩,
    rw [card_erase_of_mem ha, hs],
    refl },
  { rintro ⟨⟨t, ht, hst⟩, hs⟩,
    by_cases s ∈ 𝒜,
    { exact or.inl ⟨h, hs⟩ },
    obtain ⟨a, ha, hst⟩ := ssubset_iff.1
      (ssubset_of_subset_of_ne hst (ht.ne_of_not_mem h).symm),
    refine or.inr ⟨insert a s, ⟨⟨t, ht, hst⟩, _⟩, a, mem_insert_self _ _, erase_insert ha⟩,
    rw [card_insert_of_not_mem ha, hs] }
end

variables {𝒜 k}

/-- The shadow of `falling m 𝒜` is disjoint from the `n`-sized elements of `𝒜`, thanks to the
antichain property. -/
lemma _root_.is_antichain.disjoint_slice_shadow_falling {m n : ℕ}
  (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α))) :
  disjoint (𝒜 # m) (∂ (falling n 𝒜)) :=
disjoint_right.2 $ λ s h₁ h₂,
begin
  simp_rw [mem_shadow_iff, exists_prop, mem_falling] at h₁,
  obtain ⟨s, ⟨⟨t, ht, hst⟩, hs⟩, a, ha, rfl⟩ := h₁,
  refine h𝒜 (slice_subset h₂) ht _ ((erase_subset _ _).trans hst),
  rintro rfl,
  exact not_mem_erase _ _ (hst ha),
end

/-- A bound on any top part of the sum in LYM in terms of the size of `falling k 𝒜`. -/
lemma le_card_falling_div_choose [fintype α] (hk : k ≤ fintype.card α)
  (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α))) :
  ∑ r in range (k + 1),
    ((𝒜 # (fintype.card α - r)).card : 𝕜) / (fintype.card α).choose (fintype.card α - r)
      ≤ (falling (fintype.card α - k) 𝒜).card / (fintype.card α).choose (fintype.card α - k) :=
begin
  induction k with k ih,
  { simp only [tsub_zero, cast_one, cast_le, sum_singleton, div_one, choose_self, range_one],
    exact card_le_of_subset (slice_subset_falling _ _) },
  rw succ_eq_add_one at *,
  rw [sum_range_succ, ←slice_union_shadow_falling_succ,
    card_disjoint_union h𝒜.disjoint_slice_shadow_falling, cast_add, _root_.add_div, add_comm],
  rw [←tsub_tsub, tsub_add_cancel_of_le (le_tsub_of_add_le_left hk)],
  exact add_le_add_left ((ih $ le_of_succ_le hk).trans $ card_div_choose_le_card_shadow_div_choose
    (tsub_pos_iff_lt.2 $ nat.succ_le_iff.1 hk).ne' $ sized_falling _ _) _,
end

end falling

variables {𝒜 : finset (finset α)} {s : finset α} {k : ℕ}

/-- The **Lubell-Yamamoto-Meshalkin inequality**. If `𝒜` is an antichain, then the sum of the
proportion of elements it takes from each layer is less than `1`. -/
lemma sum_card_slice_div_choose_le_one [fintype α] (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α))) :
  ∑ r in range (fintype.card α + 1), ((𝒜 # r).card : 𝕜) / (fintype.card α).choose r ≤ 1 :=
begin
  classical,
  rw ←sum_flip,
  refine (le_card_falling_div_choose le_rfl h𝒜).trans _,
  rw div_le_iff; norm_cast,
  { simpa only [nat.sub_self, one_mul, nat.choose_zero_right, falling]
      using (sized_falling 0 𝒜).card_le },
  { rw [tsub_self, choose_zero_right],
    exact zero_lt_one }
end

end lym

/-! ### Sperner's theorem -/

/-- **Sperner's theorem**. The size of an antichain in `finset α` is bounded by the size of the
maximal layer in `finset α`. This precisely means that `finset α` is a Sperner order. -/
lemma _root_.is_antichain.sperner [fintype α] {𝒜 : finset (finset α)}
  (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α))) :
  𝒜.card ≤ (fintype.card α).choose (fintype.card α / 2) :=
begin
  classical,
  suffices : ∑ r in Iic (fintype.card α),
    ((𝒜 # r).card : ℚ) / (fintype.card α).choose (fintype.card α / 2) ≤ 1,
  { rwa [←sum_div, ←nat.cast_sum, div_le_one, cast_le, sum_card_slice] at this,
    norm_cast,
    exact choose_pos (nat.div_le_self _ _) },
  rw [Iic_eq_Icc, ←Ico_succ_right, bot_eq_zero, Ico_zero_eq_range],
  refine (sum_le_sum $ λ r hr, _).trans (sum_card_slice_div_choose_le_one h𝒜),
  rw mem_range at hr,
  refine div_le_div_of_le_left _ _ _; norm_cast,
  { exact nat.zero_le _ },
  { exact choose_pos (lt_succ_iff.1 hr) },
  { exact choose_le_middle _ _ }
end

end finset
