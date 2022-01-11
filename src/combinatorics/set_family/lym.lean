/-
Copyright (c) 2022 Bhavik Mehta, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
import algebra.big_operators.ring
import combinatorics.double_counting
import combinatorics.set_family.shadow
import data.rat.order
import tactic.linarith

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

/-- An unbundled relation class stating that `r` is the nonstrict relation corresponding to the
strict relation `s`. Compare `preorder.lt_iff_le_not_le`. This is mostly meant to be used for `(⊆)`
and `(⊂)`. -/
class is_nonstrict_strict_order (α : Type*) (r s : α → α → Prop) :=
(right_iff_left_not_left {a b : α} : s a b ↔ r a b ∧ ¬ r b a)

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

lemma ssubset_of_subset_of_ne {s t : finset α} (h₁ : s ⊆ t) (h₂ : s ≠ t) : s ⊂ t :=
lt_iff_ssubset.1 $ lt_of_le_of_ne h₁ h₂

lemma _root_.multiset.le_cons (m : multiset α) (a : α) : m ≤ a ::ₘ m :=
quotient.induction_on m $ λ l, (list.sublist_cons _ _).subperm

lemma _root_.multiset.lt_cons (m : multiset α) (a : α) : m < a ::ₘ m :=
(m.le_cons _).lt_of_not_le begin
  sorry
end

lemma _root_.multiset.subset_cons (m : multiset α) (a : α) : m ⊆ a ::ₘ m :=
λ _, multiset.mem_cons_of_mem

lemma _root_.multiset.ssubset_cons {m : multiset α} {a : α} (ha : a ∉ m) : m ⊂ a ::ₘ m :=
λ _, multiset.mem_cons_of_mem


lemma subset_cons {s : finset α} {a : α} (h : a ∉ s) : s ⊆ s.cons a h :=
multiset.subset_cons _ _

lemma ssubset_cons {s : finset α} {a : α} (h : a ∉ s) : s ⊂ s.cons a h :=
⟨subset_cons h, λ hs, h $ hs $ mem_cons_self _ _⟩

lemma ssubset_iff_exists_cons_subset {s t : finset α} :
  s ⊂ t ↔ ∃ a (h : a ∉ s), s.cons a h ⊆ t :=
begin
  refine ⟨λ h, _, _⟩,
  {
    sorry
  },
  { rintro ⟨a, ha, h⟩,
    exact ssubset_of_ssubset_of_subset (ssubset_cons _) h }
end

lemma ssubset_iff_exists_insert_subset [decidable_eq α] {s t : finset α} :
  s ⊂ t ↔ ∃ a ∉ s, insert a s ⊆ t :=
by simp_rw [ssubset_iff_exists_cons_subset, cons_eq_insert]

lemma ssubset_iff_exists_subset_erase [decidable_eq α] {s t : finset α} :
  s ⊂ t ↔ ∃ a ∈ t, s ⊆ t.erase a :=
begin
  sorry
end

lemma subset_singleton_iff' {s : finset α} {a : α} : s ⊆ {a} ↔ ∀ b ∈ s, b = a :=
forall_congr $ λ b, forall_congr $ λ _, mem_singleton

lemma _root_.has_mem.mem.ne_of_not_mem {β : Type*} [has_mem α β] {a b : α} {s : β} (ha : a ∈ s)
  (hb : b ∉ s) :
  a ≠ b :=
ne_of_mem_of_not_mem ha hb

lemma _root_.has_mem.mem.ne_of_not_mem' {β : Type*} [has_mem α β] {a : α} {s t : β} (h : a ∈ s) :
  a ∉ t → s ≠ t :=
mt $ λ e, e ▸ h

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
    obtain ⟨a, ha, hst⟩ := ssubset_iff_exists_insert_subset.1
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
lemma le_card_falling [fintype α] (hk : k ≤ fintype.card α)
  (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α))) :
  ∑ r in range (k + 1),
    ((𝒜 # (fintype.card α - r)).card : 𝕜) / (fintype.card α).choose (fintype.card α - r)
    ≤ (falling (fintype.card α - k) 𝒜).card / (fintype.card α).choose (fintype.card α - k) :=
begin
  induction k with k ih,
  { simp only [tsub_zero, cast_one, cast_le, sum_singleton, div_one, choose_self, range_one],
    exact card_le_of_subset (slice_subset_falling _ _) },
  rw [sum_range_succ, ←slice_union_shadow_falling_succ,
    card_disjoint_union h𝒜.disjoint_slice_shadow_falling, cast_add, _root_.add_div, add_comm],
  convert add_le_add_left ((ih $ k.le_succ.trans hk).trans $
    local_lym (tsub_pos_iff_lt.2 $ nat.succ_le_iff.1 hk).ne' $ sized_falling _ _) _,
end

end falling

variables {𝒜 : finset (finset α)} {s : finset α} {k : ℕ}

/-- The **Lubell-Yamamoto-Meshalkin inequality**. If `𝒜` is an antichain, then the sum of the
proportion of elements it takes from each layer is less than `1`. -/
lemma lubell_yamamoto_meshalkin [fintype α] (h𝒜 : is_antichain (⊆) (𝒜 : set (finset α))) :
  ∑ r in range (fintype.card α + 1), ((𝒜 # r).card : 𝕜) / (fintype.card α).choose r ≤ 1 :=
begin
  classical,
  rw ←sum_flip,
  refine (le_card_falling le_rfl h𝒜).trans _,
  rw div_le_iff; norm_cast,
  { simpa only [mul_one, nat.choose_zero_right, nat.sub_self]
      using (sized_falling (fintype.card α) 𝒜).card_le },
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
