/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import algebra.big_operators.order
import algebra.big_operators.ring
import combinatorics.set_family.shadow
import data.rat.order
import order.antichain

/-!
# Lubell-Yamamoto-Meshalkin inequality and Sperner's theorem

This file proves the local LYM and LYM inequalities as well as Sperner's theorem.

## Main declarations

* `local_lym`: Local Lubell-Yamamoto-Meshalkin inequality. The shadow of a set `𝒜` in a layer takes
  a greater proportion of its layer than `𝒜` does.
* `lubell_yamamoto_meshalkin`: Lubell-Yamamoto-Meshalkin inequality. The sum of the proportion of
  elements of each layers `𝒜` takes is less than `1`.
* `is_antichain.sperner`: Sperner's theorem. An antichain in `finset α` has at most the size of the
  maximal layer of `finset α` elements. It is a corollary of `lubell_yamamoto_meshalkin`.

## TODO

Prove upward local LYM.

Provide equality cases. Local LYM gives that the equality case of LYM and Sperner is precisely when
`𝒜` is a middle layer.

Most of the machinery (`from_above`, `from_below` and `falling`) is useful more generally in grade
orders.

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
variables [decidable_eq α]

private lemma lym_aux {s t n r : ℕ} (hr : r ≠ 0) (hrn : r ≤ n)
  (h : s * r ≤ t * (n - r + 1)) :
  (s : 𝕜) / nat.choose n r ≤ t / nat.choose n (r-1) :=
begin
  rw div_le_div_iff; norm_cast,
  { cases r,
    { exact (hr rfl).elim },
    rw nat.succ_eq_add_one at *,
    rw [tsub_add_eq_add_tsub hrn, add_tsub_add_eq_tsub_right] at h,
    apply le_of_mul_le_mul_right _ (pos_iff_ne_zero.2 hr),
    convert nat.mul_le_mul_right (n.choose r) h using 1,
    { simp [mul_assoc, nat.choose_succ_right_eq],
      exact or.inl (mul_comm _ _) },
    { simp only [mul_assoc, choose_succ_right_eq, mul_eq_mul_left_iff],
      exact or.inl (mul_comm _ _) } },
  { exact nat.choose_pos hrn },
  { exact nat.choose_pos (r.pred_le.trans hrn) }
end

variables {𝒜 : finset (finset α)} {r : ℕ}

/-- First set of the double counting. Effectively `{(s, t) | s ∈ 𝒜, t ∈ s.image (erase s)}`. -/
def lym_above (𝒜 : finset (finset α)) : finset (finset α × finset α) :=
𝒜.sup $ λ s, s.image $ λ x, (s, erase s x)

/-- For each `s ∈ 𝒜` there are `r` possible `t` to make an element of `lym_above`. -/
lemma _root_.set.sized.card_lym_above (h𝒜 : (𝒜 : set (finset α)).sized r) :
  (lym_above 𝒜).card = 𝒜.card * r :=
begin
  rw [lym_above, sup_eq_bUnion, card_bUnion],
  { convert sum_const_nat _,
    refine λ x hx, (card_image_of_inj_on $ λ a ha b hb h, _).trans (h𝒜 hx),
    exact x.erase_inj_on ha hb (prod.mk.inj h).2 },
  { simp only [disjoint_left, mem_image],
    rintro _ _ _ _ h a ⟨_, _, rfl⟩ ⟨_, _, a₂⟩,
    exact h (prod.mk.inj a₂.symm).1 }
end

variables [fintype α]

/-- Second set of the double counting. We're trying to get the same set, but we count `t` first, so
we overestimate a bit. It's pretty much `{(s, t) | t ∈ ∂𝒜, ∃ a ∉ t, s = t ∪ {a}}` -/
def lym_below (𝒜 : finset (finset α)) : finset (finset α × finset α) :=
(∂𝒜).sup $ λ t, tᶜ.image $ λ a, (insert a t, t)

/-- For each `t ∈ ∂𝒜`, there are `card α - r + 1` choices for what to add to it to make an element
of `lym_below`. -/
lemma _root_.set.sized.card_lym_below (h𝒜 : (𝒜 : set (finset α)).sized r) :
  (lym_below 𝒜).card = (∂𝒜).card * (fintype.card α - (r - 1)) :=
begin
  rw [lym_below, sup_eq_bUnion, card_bUnion],
  { refine sum_const_nat (λ s hs, _),
    rw [card_image_of_inj_on, card_compl, h𝒜.shadow hs],
    intros a ha b hb h,
    injection h with hab,
    have q := mem_insert_self a s,
    rw [hab, mem_insert] at q,
    exact q.resolve_right (mem_sdiff.1 ha).2 },
  intros s hs t ht hst,
  rw disjoint_left,
  simp_rw [mem_image, not_exists, exists_prop, mem_compl, exists_imp_distrib, prod.forall,
    prod.mk.inj_iff, and_imp, not_and],
  rintro _ b i hi rfl rfl j hj k,
  exact hst.symm,
end

lemma lym_above_subset_lym_below : lym_above 𝒜 ⊆ lym_below 𝒜 :=
begin
  rintro ⟨s, t⟩,
  simp only [lym_above, lym_below, mem_sup, mem_shadow_iff, true_and, and_imp,
    exists_prop, mem_sdiff, mem_image, prod.mk.inj_iff, mem_univ, exists_imp_distrib],
  rintro s hs a hx rfl rfl,
  exact ⟨s.erase a, ⟨s, hs, a, hx, rfl⟩, a, mem_compl.2 $ not_mem_erase _ _, insert_erase hx, rfl⟩,
end

/-- The downward **local LYM inequality**. `𝒜` takes up less of `α^(r)` (the finsets of card `r`)
than `∂𝒜` takes up of `α^(r - 1)`. -/
lemma local_lym (hr : r ≠ 0) (h𝒜 : (𝒜 : set (finset α)).sized r) :
  (𝒜.card : 𝕜) / (fintype.card α).choose r ≤ (∂𝒜).card / (fintype.card α).choose (r - 1) :=
begin
  obtain hr' | hr' := lt_or_le (fintype.card α) r,
  { rw [choose_eq_zero_of_lt hr', cast_zero, div_zero],
    exact div_nonneg (cast_nonneg _) (cast_nonneg _) },
  { apply lym_aux hr hr',
    rw [←h𝒜.card_lym_above, ←tsub_tsub_assoc hr' (pos_iff_ne_zero.2 hr), ←h𝒜.card_lym_below],
    exact card_le_of_subset lym_above_subset_lym_below }
end

end local_lym

/-! ### LYM inequality -/

section lym
variables [fintype α]

/-- An inductive definition, from the top down. `falling 𝒜 k` is all the sets with cardinality
`card α - k` which are a subset of something in `𝒜`. -/
def falling [decidable_eq α] (𝒜 : finset (finset α)) : Π (k : ℕ), finset (finset α)
| 0       := 𝒜 # (fintype.card α)
| (k + 1) := 𝒜 # (fintype.card α - (k + 1)) ∪ ∂ (falling k)

lemma sized_falling [decidable_eq α] (𝒜 : finset (finset α)) (k : ℕ) :
  (falling 𝒜 k : set (finset α)).sized (fintype.card α - k) :=
begin
  induction k with k ih,
  { exact sized_slice },
  { rw [falling, coe_union],
    exact set.sized_union.2 ⟨sized_slice, ih.shadow⟩ }
end

lemma not_subset_of_mem_slice_of_mem_shadow_falling [decidable_eq α] {𝒜 : finset (finset α)}
  {r k : ℕ} (hk : k ≤ fintype.card α) (hr : r < k) (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α)))
  {s t : finset α} (hs : s ∈ 𝒜 # (fintype.card α - k)) (ht : t ∈ ∂ (falling 𝒜 r)) :
  ¬ s ⊆ t :=
begin
  intros hst,
  obtain ⟨u, hu, htu⟩ := exists_subset_of_mem_shadow ht,
  have hsu := hst.trans htu,
  clear ht hst htu t,
  induction r with r ih generalizing s u;
  rw falling at hu,
  any_goals { rw mem_union at hu, cases hu },
  any_goals
  { refine h𝒜 (mem_slice.1 hs).1 (mem_slice.1 hu).1 (ne_of_mem_slice hs hu $ ne_of_lt _) hsu },
  { exact tsub_lt_self (hr.trans_le hk) hr },
  { mono },
  { obtain ⟨v, hv, huv⟩ := exists_subset_of_mem_shadow hu,
    exact ih (lt_of_succ_lt hr) _ hs hv (hsu.trans huv) }
end

/-- `falling 𝒜 k` is disjoint from the` n - (k + 1)`-sized elements of `𝒜`, thanks to the antichain
property. -/
lemma _root_.is_antichain.disjoint_falling_slice [decidable_eq α] {𝒜 : finset (finset α)} {k : ℕ}
  (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α))) (hk : k < fintype.card α) :
  disjoint (∂ (falling 𝒜 k)) (𝒜 # (fintype.card α - (k + 1))) :=
disjoint_right.2 $ λ s hs ht,
  not_subset_of_mem_slice_of_mem_shadow_falling hk (lt_add_one k) h𝒜 hs ht (subset.refl _)

/-- A bound on any top part of the sum in LYM in terms of the size of `falling 𝒜 k`. -/
lemma le_card_falling [decidable_eq α] {𝒜 : finset (finset α)} {k : ℕ} (hk : k ≤ fintype.card α)
  (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α))) :
  ∑ r in range (k + 1),
    ((𝒜 # (fintype.card α - r)).card : 𝕜) / (fintype.card α).choose (fintype.card α - r)
    ≤ (falling 𝒜 k).card / (fintype.card α).choose (fintype.card α - k) :=
begin
  induction k with k ih,
  { simp [falling] },
  rw [sum_range_succ, falling, union_comm, card_disjoint_union (h𝒜.disjoint_falling_slice hk),
    cast_add, _root_.add_div],
  exact add_le_add_right ((ih $ k.le_succ.trans hk).trans $
    local_lym (tsub_pos_iff_lt.2 $nat.succ_le_iff.1 hk).ne' $ sized_falling _ _) _,
end

/-- The **Lubell-Yamamoto-Meshalkin inequality**. If `𝒜` is an antichain, then the sum of the
proportion of elements it takes from each layer is less than `1`. -/
lemma lubell_yamamoto_meshalkin {𝒜 : finset (finset α)}
  (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α))) :
  ∑ r in range (fintype.card α + 1), ((𝒜 # r).card : 𝕜) / (fintype.card α).choose r ≤ 1 :=
begin
  classical,
  rw ←sum_flip,
  refine (le_card_falling le_rfl h𝒜).trans _,
  rw div_le_iff; norm_cast,
  { simpa only [mul_one, nat.choose_zero_right, nat.sub_self]
      using (sized_falling 𝒜 (fintype.card α)).card_le },
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
  suffices : ∑ r in range (fintype.card α + 1),
    ((𝒜 # r).card : ℚ) / (fintype.card α).choose (fintype.card α / 2) ≤ 1,
  { rwa [←sum_div, ←nat.cast_sum, div_le_one, cast_le, sum_card_slice] at this,
    norm_cast,
    exact choose_pos (nat.div_le_self _ _) },
  refine (sum_le_sum $ λ r hr, _).trans (lubell_yamamoto_meshalkin h𝒜),
  rw mem_range at hr,
  refine div_le_div_of_le_left _ _ _; norm_cast,
  { exact nat.zero_le _ },
  { exact choose_pos (lt_succ_iff.1 hr) },
  { exact choose_le_middle _ _ }
end

end finset
