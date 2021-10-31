/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Alena Gusakov
-/

import data.fintype.basic
import data.nat.choose
import order.antichain

/-!
# Shadows

This file defines shadows of a set family and proves the local LYM and LYM theorems, as well as
Sperner's theorem.

## Main definitions

The `shadow` of a set family is everything we can get by removing an element from each set.

The rth slice of a set family 𝒜 is given by `slice 𝒜 r`, and is the subset of its elements which
have cardinality `r`.

## Main statements

* `local_lym`
* `lubell_yamamoto_meshalkin`
* `sperner`

## Notation

We introduce the notation ∂ to denote the shadow.
We also maintain the convention that A, B, ... denote sets (usually finset α),
𝒜, ℬ, ... denote set families, i.e. `finset (finset α)` and lower-case letters
denote elements of the ground set α.

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, lym, slice, sperner, antichain
-/

open finset fintype nat

variables {α : Type*}

/-!
### Shadows

The shadow of a set family is everything we can get by removing an element
from each set.

This section develops the introductory theory of shadows, with some lemmas on
iterated shadows as well.
-/

section shadow
variables [decidable_eq α]

/-- Everything we get by removing one element from the set `A`, used to define the shadow. -/
def all_removals (A : finset α) : finset (finset α) := A.image (erase A)

/-- `B ∈ all_removals A` iff we can remove something from `A` to get `B`. -/
lemma mem_all_removals {A : finset α} {B : finset α} :
  B ∈ all_removals A ↔ ∃ i ∈ A, erase A i = B :=
by simp only [all_removals, mem_image]

/-- If `A` has size `r`, then there are `r` things we get by removing one element. -/
lemma card_all_removals {A : finset α} {r : ℕ} (H : A.card = r) :
  (all_removals A).card = r :=
begin
  rwa [all_removals, card_image_of_inj_on],
  intros i ih j _ k,
  have q: i ∉ erase A j := k ▸ not_mem_erase i A,
  rw [mem_erase, not_and] at q,
  by_contra a,
  apply q a ih
end

/-- The shadow of a set family `𝒜` is all sets we can get by removing one element
from any set in `𝒜`, and the (`k` times) iterated shadow is all sets we can get
by removing k elements from any set in `𝒜`. -/
def shadow (𝒜 : finset (finset α)) : finset (finset α) := 𝒜.sup all_removals

reserve prefix `∂`:90
notation ∂𝒜 := shadow 𝒜

/-- Shadow of the empty set is empty. -/
lemma shadow_empty : shadow (∅ : finset (finset α)) = ∅ := rfl

/-- Iterated shadow of the empty set is empty. -/
lemma iter_shadow_empty (k : ℕ) : shadow^[k] (∅ : finset (finset α)) = ∅ :=
begin
  induction k with k ih,
  { refl },
  { rwa [iterate, shadow_empty] }
end

/-- The shadow is monotonic (though not strictly so). -/
lemma shadow_monotone {𝒜 ℬ : finset (finset α)} (h : 𝒜 ⊆ ℬ) : ∂𝒜 ⊆ ∂ℬ :=
le_iff_subset.1 $ sup_mono h

/-- `B ∈ ∂𝒜` iff there is an `A ∈ 𝒜` from which we can remove something to get `B`.
-/
lemma mem_shadow {𝒜 : finset (finset α)} (B : finset α) :
  B ∈ shadow 𝒜 ↔ ∃ A ∈ 𝒜, ∃ i ∈ A, erase A i = B :=
by simp only [shadow, all_removals, mem_sup, mem_image]

/-- Alternatively, `B ∈ ∂𝒜` iff we can put something new into `B`, and land in `𝒜`. -/
lemma mem_shadow' {𝒜 : finset (finset α)} {B : finset α} :
  B ∈ shadow 𝒜 ↔ ∃ j ∉ B, insert j B ∈ 𝒜 :=
begin
  rw mem_shadow,
  split,
  { rintro ⟨A, HA, i, Hi, k⟩,
    rw ← k,
    refine ⟨i, not_mem_erase i A, _⟩,
    rwa insert_erase Hi },
  { rintro ⟨i, Hi, k⟩,
    refine ⟨insert i B, k, i, mem_insert_self _ _, _⟩,
    rw erase_insert Hi }
end

/-- `B ∈ ∂𝒜` iff `B` is exactly one element less than something from `𝒜` -/
lemma sub_iff_shadow_one {𝒜 : finset (finset α)} {B : finset α} :
  B ∈ ∂𝒜 ↔ ∃ A ∈ 𝒜, B ⊆ A ∧ (A \ B).card = 1 :=
begin
  rw mem_shadow',
  split,
  { rintro ⟨i, ih, inA⟩,
    refine ⟨insert i B, inA, subset_insert _ _, _⟩,
    rw card_sdiff (subset_insert _ _),
    simp [card_insert_of_not_mem ih] },
  { rintro ⟨A, hA, a_h_h⟩,
    rw card_eq_one at a_h_h,
    rcases a_h_h with ⟨subs, j, eq⟩,
    refine ⟨j, _, _⟩,
    { intro a,
      have : j ∉ A \ B := not_mem_sdiff_of_mem_right a,
      apply this,
      rw eq,
      apply mem_singleton_self },
    { rwa [insert_eq j B, ← eq, sdiff_union_of_subset subs] } },
end

/--
In particular, being in the shadow means we're a subset of something in `𝒜`.
-/
lemma sub_of_shadow {𝒜 : finset (finset α)} {B : finset α} :
  B ∈ ∂𝒜 → ∃ A ∈ 𝒜, B ⊆ A :=
by rw sub_iff_shadow_one; tauto

/-- `B ∈ ∂^k 𝒜` iff `B` is exactly `k` elements less than something from `𝒜`. -/
lemma sub_iff_shadow_iter {𝒜 : finset (finset α)} {B : finset α} (k : ℕ) :
  B ∈ (shadow^[k] 𝒜) ↔ ∃ A ∈ 𝒜, B ⊆ A ∧ (A \ B).card = k :=
begin
  induction k with k ih generalizing 𝒜 B,
  { simp [sdiff_eq_empty_iff_subset],
    split,
    { intro p,
      exact ⟨B, p, subset.refl _, subset.refl _⟩ },
    { rintro ⟨A, _, q⟩,
      rw ← subset.antisymm_iff at q,
      rwa q } },
  { simp only [exists_prop, function.comp_app, function.iterate_succ],
    rw @ih (∂𝒜) B,
    clear ih,
    split,
    { rintro ⟨A, hA, BsubA, card_AdiffB_is_k⟩,
      rw sub_iff_shadow_one at hA,
      rcases hA with ⟨C, CinA, AsubC, card_CdiffA_is_1⟩,
      refine ⟨C, CinA, trans BsubA AsubC, _⟩,
      rw card_sdiff (trans BsubA AsubC),
      rw card_sdiff BsubA at card_AdiffB_is_k,
      rw card_sdiff AsubC at card_CdiffA_is_1,
      rw [← nat.sub_add_cancel (card_le_of_subset AsubC),
          nat.add_sub_assoc (card_le_of_subset BsubA), card_CdiffA_is_1,
          card_AdiffB_is_k, add_comm] },
    { rintro ⟨A, hA, hBA, hAB⟩,
      have z: (A \ B).nonempty,
      { rw [← finset.card_pos, hAB],
        exact nat.succ_pos _ },
      rcases z with ⟨i, hi⟩,
      have: i ∈ A, rw mem_sdiff at hi,
      { exact hi.1 },
      have: B ⊆ erase A i,
      { intros t th,
        apply mem_erase_of_ne_of_mem _ (hBA th),
        intro a,
        rw mem_sdiff at hi,
        rw a at th,
        exact hi.2 th },
      refine ⟨erase A i, _, ‹_›, _⟩,
      { rw mem_shadow,
        refine ⟨A, hA, i, ‹_›, rfl⟩ },
      rw [card_sdiff ‹B ⊆ erase A i›,
        card_erase_of_mem ‹i ∈ A›, nat.pred_sub,
        ← card_sdiff hBA, hAB],
      simp } }
end

end shadow

/-!
### Build up and proof of local LYM

If there is a fintype α which is our universe, informally write `α^(r)` for the
`set {A : finset α | |A| = r}`. Then if `𝒜` is a subset of `α^(r)`, we get that `∂𝒜`
is a subset of `α^(r-1)`.
The local LYM inequality says `𝒜` 'takes up less' of `α^(r)` than `∂𝒜` takes up of
`α^(r-1)`. In particular,
`|𝒜| / choose |α| r ≤ |∂𝒜| / choose |α| (r-1)`
-/
section local_lym
variables [decidable_eq α]

/-- Start by multiplying out the inequality so it's in a slightly nicer form. -/
lemma multiply_out {A B n r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ n)
  (h : A * r ≤ B * (n - r + 1)) :
  (A : ℚ) / nat.choose n r ≤ B / nat.choose n (r-1) :=
begin
  rw div_le_div_iff; norm_cast,
  { apply le_of_mul_le_mul_right _ ‹0 < r›,
    cases r,
    { simp },
    { rw nat.succ_eq_add_one at *,
      rw [← nat.sub_add_comm hr2, nat.add_sub_add_right] at h,
      convert nat.mul_le_mul_right (choose n r) h using 1;
      { simp [mul_assoc, nat.choose_succ_right_eq],
        left,
        ac_refl } } },
  { apply nat.choose_pos hr2 },
  { apply nat.choose_pos (le_trans (nat.pred_le _) hr2) },
end

/-- We'll prove local LYM by a double counting argument. Here's the first set
we'll count, which is effectively `{(A, B) | A ∈ 𝒜, B ∈ all_removals A}`. -/
def the_pairs (𝒜 : finset (finset α)) : finset (finset α × finset α) :=
𝒜.sup (λ A, (all_removals A).image (prod.mk A))

/--
Here's the second set we'll count. We're trying to get the same set, but we
count B first, so we overestimate a bit. It's pretty much
{(A,B) | B ∈ ∂𝒜, ∃ i ∉ B: A = B ∪ i}
-/
def from_below [fintype α] (𝒜 : finset (finset α)) :
  finset (finset α × finset α) :=
(∂𝒜).sup (λ B, (univ \ B).image (λ x, (insert x B, B)))

/--
Note the first is a subset of the second: if A ∈ 𝒜 and B ∈ all_removals A
then certainly B ∈ ∂𝒜, and there's some i that was removed from A to make B.
-/
lemma above_sub_below [fintype α] (𝒜 : finset (finset α)) :
  the_pairs 𝒜 ⊆ from_below 𝒜 :=
begin
  rintro ⟨A,B⟩,
  simp only [the_pairs, from_below, mem_sup, mem_all_removals, mem_shadow, true_and, and_imp,
    exists_prop, mem_sdiff, mem_image, prod.mk.inj_iff, mem_univ, exists_imp_distrib],
  rintro A Ah B i ih z rfl rfl,
  exact ⟨B, ⟨A, Ah, i, ih, z⟩, i, z ▸ not_mem_erase _ _,
          z ▸ insert_erase ih, rfl⟩
end

end local_lym
