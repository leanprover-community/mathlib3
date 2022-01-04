/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import combinatorics.set_family.shadow
import data.fintype.basic
import data.nat.choose
import order.antichain

/-!
# Lubell-Yamamoto-Meshalkin inequality and Sperner's

This file proves the local LYM and LYM inequalities as well as Sperner's theorem.

## Main declarations

* `local_lym`: Local Lubell-Yamamoto-Meshalkin inequality. The shadow of a set
* `lubell_yamamoto_meshalkin`
* `is_antichain.sperner`: Sperner's theorem

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, lym, slice, sperner, antichain
-/

open finset fintype nat
open_locale finset_family

variables {α : Type*}

/-!
### Build up and proof of local LYM

If there is a fintype α which is our universe, informally write `α^(r)` for the
`set {s : finset α | |s| = r}`. Then if `𝒜` is a subset of `α^(r)`, we get that `∂𝒜`
is a subset of `α^(r-1)`.
The local LYM inequality says `𝒜` 'takes up less' of `α^(r)` than `∂𝒜` takes up of
`α^(r-1)`. In particular,
`|𝒜| / choose |α| r ≤ |∂𝒜| / choose |α| (r-1)`
-/

namespace finset

section local_lym
variables [decidable_eq α]

/-- Start by multiplying out the inequality so it's in a slightly nicer form. -/
lemma multiply_out {s t n r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n)
  (h : s * r ≤ t * (n - r + 1)) :
  (s : ℚ) / nat.choose n r ≤ t / nat.choose n (r-1) :=
begin
  rw div_le_div_iff; norm_cast,
  { apply le_of_mul_le_mul_right _ ‹0 < r›,
    cases r,
    { simp },
    rw nat.succ_eq_add_one at *,
    rw [←nat.sub_add_comm hrn, nat.add_sub_add_right] at h,
    convert nat.mul_le_mul_right (n.choose r) h using 1;
    { simp [mul_assoc, nat.choose_succ_right_eq],
      left,
      ac_refl } },
  { exact nat.choose_pos hrn },
  { exact nat.choose_pos (le_trans (nat.pred_le _) hrn) }
end

variables {𝒜 : finset (finset α)} {r : ℕ}

/-- We'll prove local LYM by a double counting argument. Here's the first set
we'll count, which is effectively `{(s, t) | s ∈ 𝒜, t ∈ s.image (erase s)}`. -/
def lym_above (𝒜 : finset (finset α)) : finset (finset α × finset α) :=
𝒜.sup $ λ s, s.image $ λ x, (s, erase s x)

/-- Find how big `lym_above` is: for each `s ∈ 𝒜` there are `r` possible `t`, giving the
exact cardinality. -/
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

/-- Here's the second set we'll count. We're trying to get the same set, but we count `t` first, so
we overestimate a bit. It's pretty much `{(s, t) | t ∈ ∂𝒜, ∃ a ∉ t: s = t ∪ {a}}` -/
def lym_below (𝒜 : finset (finset α)) : finset (finset α × finset α) :=
(∂𝒜).sup $ λ t, tᶜ.image $ λ a, (insert a t, t)

lemma lym_above_subset_lym_below : lym_above 𝒜 ⊆ lym_below 𝒜 :=
begin
  rintro ⟨s, t⟩,
  simp only [lym_above, lym_below, mem_sup, mem_shadow_iff, true_and, and_imp,
    exists_prop, mem_sdiff, mem_image, prod.mk.inj_iff, mem_univ, exists_imp_distrib],
  rintro s hs a hx rfl rfl,
  exact ⟨s.erase a, ⟨s, hs, a, hx, rfl⟩, a, mem_compl.2 $ not_mem_erase _ _, insert_erase hx, rfl⟩,
end

/-- We can also find how big the second set is: for each `t` there are `|α| - r + 1` choices for
what to put into it. -/
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

/-- The downward **local LYM inequality**. `𝒜` takes up less of `α^(r)` than `∂𝒜` takes up of
`α^(r - 1)`. -/
lemma local_lym (hr : 1 ≤ r) (h𝒜 : (𝒜 : set (finset α)).sized r) :
  (𝒜.card : ℚ) / (fintype.card α).choose r ≤ (∂𝒜).card / (fintype.card α).choose (r - 1) :=
begin
  cases lt_or_le (fintype.card α) r with z hr',
  -- Take care of the r > n case: it's trivial
  { rw [choose_eq_zero_of_lt z, cast_zero, div_zero],
    refine div_nonneg _ _; norm_cast,
    any_goals { apply nat.zero_le } },
  { apply multiply_out hr hr',
  -- Multiply out, convert to the cardinality forms we got above and done
    rw [←h𝒜.card_lym_above, ←tsub_tsub_assoc hr' hr, ←h𝒜.card_lym_below],
    exact card_le_of_subset lym_above_subset_lym_below }
end

/-- The upward **local LYM inequality**. `𝒜` takes up less of `α^(r)` than `∂⁺𝒜` takes up of
`α^(r + 1)`. -/
lemma local_up_lym (hr : r < fintype.card α) (h𝒜 : (𝒜 : set (finset α)).sized r) :
  (𝒜.card : ℚ) / (fintype.card α).choose r ≤ (∂⁺𝒜).card / (fintype.card α).choose (r + 1) :=
begin
  obtain rfl | hr₀ := r.eq_zero_or_pos,
  { rw [choose_zero_right, cast_one, div_one],
    refine div_nonneg _ _; norm_cast,
    any_goals { apply nat.zero_le } },
  { apply multiply_out hr hr',
  -- Multiply out, convert to the cardinality forms we got above and done
    rw [←h𝒜.card_lym_above, ←tsub_tsub_assoc hr' hr, ←h𝒜.card_lym_below],
    exact card_le_of_subset lym_above_subset_lym_below }
end

end local_lym

/-!
The LYM inequality says ∑_i |s#i|/(n choose i) ≤ 1 for an antichain s.
Observe that s#i is all the stuff in s which has size i, and the collection of
subsets of (fin n) with size i has size (n choose i).
So, |s#i|/(n choose i) represents how much of each that s can take up.

Other proofs of LYM exist, but we'll do it by applying local LYM.
-/
section lym

variables [fintype α]

/-- An inductive definition, from the top down.
`falling 𝒜 k` is all the sets with cardinality (card α - k) which are a
subset of something in 𝒜. -/
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

/--
Here's the first key proposition, helping to give the disjointness
property in the next lemma.
-/
lemma antichain_prop [decidable_eq α] {𝒜 : finset (finset α)} {r k : ℕ}
  (hk : k ≤ fintype.card α) (hr : r < k) (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α)))
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

/-- This tells us that `falling 𝒜 k` is disjoint from the` n - (k + 1)`-sized elements of `𝒜`,
thanks to the antichain property. -/
lemma _root_.is_antichain.disjoint_falling_slice [decidable_eq α] {𝒜 : finset (finset α)} {k : ℕ}
  (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α))) (hk : k < fintype.card α) :
  disjoint (∂ (falling 𝒜 k)) (𝒜 # (fintype.card α - (k + 1))) :=
disjoint_right.2 $ λ s hs ht, antichain_prop hk (lt_add_one k) h𝒜 hs ht (subset.refl _)

/-- In particular, we can use induction and local LYM to get a bound on any top
part of the sum in LYM in terms of the size of `falling 𝒜 k`. -/
lemma card_falling [decidable_eq α] {𝒜 : finset (finset α)} {k : ℕ} (hk : k ≤ fintype.card α)
  (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α))) :
  (range (k + 1)).sum
    (λ r, ((𝒜 # (fintype.card α - r)).card : ℚ) / (fintype.card α).choose (fintype.card α - r))
  ≤ (falling 𝒜 k).card / (fintype.card α).choose (fintype.card α - k) :=
begin
  induction k with k ih,
  { simp [falling] },
  rw [sum_range_succ, falling, union_comm, card_disjoint_union (h𝒜.disjoint_falling_slice hk),
    cast_add, _root_.add_div],
  exact add_le_add_right
    ((ih $ k.le_succ.trans hk).trans $ local_lym (le_tsub_of_add_le_left hk) $ sized_falling _ _) _,
end

/-- s stepping-stone lemma to get to LYM. -/
lemma card_fallen [decidable_eq α] {𝒜 : finset (finset α)}
  (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α))) :
  (range (fintype.card α + 1)).sum (λ r, ((𝒜 # r).card : ℚ) / (fintype.card α).choose r)
  ≤ (falling 𝒜 (fintype.card α)).card / (fintype.card α).choose 0 :=
begin
  rw [←nat.sub_self (fintype.card α)],
  convert ←card_falling le_rfl h𝒜 using 1,
  apply sum_flip (λ r, ((𝒜 # r).card : ℚ) / (fintype.card α).choose r),
end

/-- The LYM inequality says `∑_i |s#i|/(n choose i) ≤ 1` for an antichain `s`.
Observe that `s#i` is all the stuff in `s` which has size `i`, and the collection of
sets of `fin n` with size `i` has size `n choose i`.
So `|s#i|/(n choose i)` represents how much of each `s` can take up.

The proof is easy using the developed lemmas above. -/
lemma lubell_yamamoto_meshalkin {𝒜 : finset (finset α)}
  (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α))) :
  (range (fintype.card α + 1)).sum (λ r, ((𝒜 # r).card : ℚ) / (fintype.card α).choose r) ≤ 1 :=
begin
  classical,
  transitivity,
  { apply card_fallen h𝒜 },
  rw div_le_iff; norm_cast,
  { simpa only [mul_one, nat.choose_zero_right, nat.sub_self]
      using (sized_falling 𝒜 (fintype.card α)).card_le },
  exact nat.choose_pos (nat.zero_le _),
end

end lym

/-- Sperner's lemma gives a bound on the size of an antichain. This can be proved in a few ways,
but this uses the machinery already developed about LYM. The idea is simple: with LYM, we get a
bound on how much of `s` can have any particular size.  So, to maximise the size of s, we'd like to
fit it all into the term with the biggest denominator. In other words,
`∑_i |s#i|/(n choose (n/2)) ≤ ∑_i |s#i|/(n choose i) ≤ 1`, so `∑_i |s#i| ≤ (n choose (n/2))` as
required. -/
lemma is_antichain.sperner [fintype α] {𝒜 : finset (finset α)}
  (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α))) :
  𝒜.card ≤ (fintype.card α).choose (fintype.card α / 2) :=
begin
  classical,
  have : (range (fintype.card α + 1)).sum (λ (r : ℕ), ((𝒜 # r).card : ℚ) /
    (fintype.card α).choose (fintype.card α/2)) ≤ 1,
  { apply le_trans _ (lubell_yamamoto_meshalkin h𝒜),
    apply sum_le_sum,
    intros r hr,
    apply div_le_div_of_le_left; norm_cast,
    { apply nat.zero_le },
    { apply choose_pos, rw mem_range at hr, rwa ←nat.lt_succ_iff },
    { apply choose_le_middle } },
  rw [←sum_div, ←nat.cast_sum, div_le_one] at this,
  { norm_cast at this,
    rw ←card_bUnion at this,
    convert this,
    simp only [ext_iff, mem_slice, mem_bUnion, exists_prop, mem_range, lt_succ_iff],
    refine λ a, ⟨λ ha, ⟨a.card, card_le_of_subset (subset_univ _), ha, rfl⟩, _⟩,
    rintro ⟨_, _, q, _⟩,
    exact q,
    intros x _ y _ ne,
    rw disjoint_left,
    intros a ha k,
    exact ne_of_mem_slice ha k ne rfl },
  { norm_cast,
    exact choose_pos (nat.div_le_self _ _) }
end

end finset
