/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import algebra.big_operators.ring
import combinatorics.double_counting
import combinatorics.set_family.shadow
import data.rat.order

/-!
# Lubell-Yamamoto-Meshalkin inequality and Sperner's theorem

This file proves the local LYM and LYM inequalities as well as Sperner's theorem.

## Main declarations

* `local_lym`: Local Lubell-Yamamoto-Meshalkin inequality. The shadow of a set `𝒜` in a layer takes
  a greater proportion of its layer than `𝒜` does.
* `lubell_yamamoto_meshalkin`: Lubell-Yamamoto-Meshalkin inequality. The sum of densities of `𝒜`
  in each layer is at most `1` for any antichain `𝒜`.
* `is_antichain.sperner`: Sperner's theorem. The size of any antichain in `finset α` is at most
  the size of the maximal layer of `finset α`. It is a corollary of `lubell_yamamoto_meshalkin`.

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

-- generalize `tsub_le_tsub_left` to `preorder`
-- generalize `tsub_le_iff_left` to `add_comm_semigroup`

lemma tsub_tsub_le_tsub_add [preorder α] [add_comm_monoid α] [has_sub α] [has_ordered_sub α]
  [covariant_class α α (+) (≤)] {a b c : α} :
  a - (b - c) ≤ a - b + c :=
tsub_le_iff_right.2 $ calc
    a ≤ a - b + b : le_tsub_add
  ... ≤ a - b + (c + (b - c)) : add_le_add_left le_add_tsub _
  ... = a - b + c + (b - c) : (add_assoc _ _ _).symm

-- lemma tsub_tsub_le_tsub_add' [preorder α] [add_comm_monoid α] [has_sub α] [has_ordered_sub α]
--   [covariant_class α α (+) (≤)] {a b c : α} :
--   a - (b - c) ≤ a - b + c :=
-- by { rw [←tsub_le_iff_right], have := tsub_tsub,
--     sorry,
--  exact tsub_le_tsub_left le_tsub_add _ }

namespace finset

/-- The only element of `insert a s` that is not an element of `s` is `a`. -/
lemma eq_of_not_mem_of_mem_insert [decidable_eq α] {a b : α} {s : finset α} (hb : b ∉ s)
  (ha : b ∈ insert a s) :
  b = a :=
(mem_insert.1 ha).resolve_right hb

lemma insert_inj [decidable_eq α] {a b : α} {s : finset α} (ha : a ∉ s) :
  insert a s = insert b s ↔ a = b :=
begin
  refine ⟨λ h, eq_of_not_mem_of_mem_insert ha _, congr_arg _⟩,
  rw ←h,
  exact mem_insert_self _ _,
end

lemma insert_inj_on' [decidable_eq α] (s : finset α) : set.inj_on (λ a, insert a s) sᶜ :=
λ a ha b _, (insert_inj ha).1

lemma insert_inj_on [decidable_eq α] [fintype α] (s : finset α) :
  set.inj_on (λ a, insert a s) (sᶜ : finset α) :=
by { rw coe_compl, exact s.insert_inj_on' }

@[simp]
lemma card_erase_of_mem' [decidable_eq α] {a : α} {s : finset α} (ha : a ∈ s) :
  (s.erase a).card = s.card - 1 :=
card_erase_of_mem ha

lemma sdiff_nonempty [decidable_eq α] {s t : finset α} : (s \ t).nonempty ↔ ¬ s ⊆ t :=
by rw [nonempty_iff_ne_empty, ne.def, sdiff_eq_empty_iff_subset]

lemma exists_eq_insert_iff [decidable_eq α] {s t : finset α} :
  (∃ a ∉ s, insert a s = t) ↔ s ⊆ t ∧ s.card + 1 = t.card :=
begin
  refine ⟨_, _⟩,
  { rintro ⟨a, ha, rfl⟩,
    exact ⟨subset_insert _ _, (card_insert_of_not_mem ha).symm⟩ },
  { rintro ⟨hst, h⟩,
    obtain ⟨a, ha⟩ : ∃ a, t \ s = {a},
    { exact card_eq_one.1 (by rw [card_sdiff hst, ←h, add_tsub_cancel_left]) },
    refine ⟨a, λ hs, (_ : a ∉ {a}) $ mem_singleton_self _,
      by rw [insert_eq, ←ha, sdiff_union_of_subset hst]⟩,
    rw ←ha,
    exact not_mem_sdiff_of_mem_right hs }
end

/-! ### Local LYM inequality -/

section local_lym
variables [decidable_eq α] [fintype α] {𝒜 : finset (finset α)} {r : ℕ}

/-- The downward **local LYM inequality**, with cancelled denominators. `𝒜` takes up less of `α^(r)`
(the finsets of card `r`) than `∂𝒜` takes up of `α^(r - 1)`. -/
lemma local_lym' (h𝒜 : (𝒜 : set (finset α)).sized r) :
  𝒜.card * r ≤ (∂𝒜).card * (fintype.card α - r + 1) :=
begin
  refine card_mul_le_card_mul' (⊆) (λ s hs, _) (λ s hs, _),
  { rw [←h𝒜 hs, ←card_image_of_inj_on s.erase_inj_on],
    refine card_le_of_subset _,
    simp_rw [image_subset_iff, mem_bipartite_below],
    exact λ a ha, ⟨erase_mem_shadow hs ha, erase_subset _ _⟩ },
  refine le_trans _ tsub_tsub_le_tsub_add,
  rw [←h𝒜.shadow hs, ←card_compl, ←card_image_of_inj_on (insert_inj_on _)],
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
lemma local_lym (hr : r ≠ 0) (h𝒜 : (𝒜 : set (finset α)).sized r) :
  (𝒜.card : 𝕜) / (fintype.card α).choose r ≤ (∂𝒜).card / (fintype.card α).choose (r - 1) :=
begin
  obtain hr' | hr' := lt_or_le (fintype.card α) r,
  { rw [choose_eq_zero_of_lt hr', cast_zero, div_zero],
    exact div_nonneg (cast_nonneg _) (cast_nonneg _) },
  replace h𝒜 := local_lym' h𝒜,
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
