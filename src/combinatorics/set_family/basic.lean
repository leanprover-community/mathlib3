/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import combinatorics.set_family.shadow
import data.fintype.basic

/-!
# Basic definitions for finite sets which are useful for combinatorics

We define a proposition asserting that a set is a set of r-sets.
-/

open finset nat
open_locale finset_family

variables {α : Type*}

namespace finset

section sized
variables {A B : finset (finset α)} {r : ℕ}

/-! ### Sized -/

/-- `sized A r` states that every set in A has size r. -/
def sized (A : finset (finset α)) (r : ℕ) : Prop := ∀ ⦃x⦄, x ∈ A → card x = r

lemma sized.mono (h : A ⊆ B) (hB : B.sized r) : A.sized r := λ x hx, hB $ h hx

/-- All sets in the union have size `r` iff both sets individually have this property. -/
lemma sized_union [decidable_eq α] : sized (A ∪ B) r ↔ sized A r ∧ sized B r :=
begin
  refine ⟨λ hA, ⟨hA.mono $ subset_union_left _ _, hA.mono $ subset_union_right _ _⟩, λ hA x hx, _⟩,
  rw mem_union at hx,
  exact hx.elim (λ h, hA.1 h) (λ h, hA.2 h),
end

variables [fintype α] {𝒜 : finset (finset α)} {s : finset α}

lemma mem_powerset_len_univ_iff : s ∈ powerset_len r (univ : finset α) ↔ card s = r :=
mem_powerset_len.trans $ and_iff_right (subset_univ _)

lemma subset_powerset_len_univ_iff : 𝒜 ⊆ powerset_len r univ ↔ sized 𝒜 r :=
by rw sized; apply forall_congr _; intro A; rw mem_powerset_len_univ_iff

alias subset_powerset_len_univ_iff  ↔ _ finset.sized.subset_powerset_len_univ

lemma sized.card_le (h𝒜 : sized 𝒜 r) : card 𝒜 ≤ (fintype.card α).choose r :=
begin
  rw [fintype.card, ←card_powerset_len],
  exact card_le_of_subset h𝒜.subset_powerset_len_univ,
end

end sized

/-!
### Slices

The `r`th slice of a set family the subset of its elements which have
cardinality `r`.
A few basic facts about slices.
-/
section slice
variables {𝒜 : finset (finset α)} {A : finset α} {r : ℕ}

/-- The `r`th slice of a set family the subset of its elements which have cardinality `r`. -/
def slice (𝒜 : finset (finset α)) (r : ℕ) : finset (finset α) := 𝒜.filter (λ i, i.card = r)

localized "infix ` # `:90 := finset.slice" in finset_family

/-- `A` is in the `r`th slice of `𝒜` iff it's in `𝒜` and has cardinality `r`. -/
lemma mem_slice : A ∈ 𝒜 # r ↔ A ∈ 𝒜 ∧ A.card = r := mem_filter

/-- The `r`th slice of `𝒜` is a subset of `𝒜`. -/
lemma slice_subset : 𝒜#r ⊆ 𝒜 := filter_subset _ _

/-- Everything in the `r`th slice of `𝒜` has size `r`. -/
lemma sized_slice : sized (𝒜#r) r := λ _, and.right ∘ mem_slice.mp

/-- Elements in distinct slices must be distinct. -/
lemma ne_of_diff_slice {𝒜 : finset (finset α)} {r₁ r₂ : ℕ}
  {A₁ A₂ : finset α} (h₁ : A₁ ∈ 𝒜#r₁) (h₂ : A₂ ∈ 𝒜#r₂) :
  r₁ ≠ r₂ → A₁ ≠ A₂ :=
mt $ λ h, (sized_slice h₁).symm.trans ((congr_arg card h).trans (sized_slice h₂))

variables [decidable_eq α]

lemma pairwise_disjoint_slice : (set.univ : set ℕ).pairwise_disjoint (slice 𝒜) :=
λ m _ n _ hmn, disjoint_filter.2 $ λ s hs hm hn, hmn $ hm.symm.trans hn

end slice

variables [decidable_eq α] {𝒜 : finset (finset α)} {A B : finset α} {r k : ℕ}

/-- Iterated shadow of the empty set is empty. -/
lemma iter_shadow_empty (k : ℕ) : shadow^[k] (∅ : finset (finset α)) = ∅ :=
begin
  induction k with k ih,
  { refl },
  { rwa [iterate, shadow_empty] }
end

/-- Everything in the shadow is one smaller than things in the original. -/
lemma sized.shadow (h𝒜 : sized 𝒜 r) : sized (∂𝒜) (r - 1) :=
begin
  intros A h,
  obtain ⟨A, hA, i, hi, rfl⟩ := mem_shadow_iff.1 h,
  rw [card_erase_of_mem hi, h𝒜 hA],
  refl,
end

/-- `B ∈ ∂𝒜` iff `B` is exactly one element less than something from `𝒜` -/
lemma sub_iff_shadow_one : B ∈ ∂𝒜 ↔ ∃ A ∈ 𝒜, B ⊆ A ∧ (A \ B).card = 1 :=
begin
  rw mem_shadow_iff_insert_mem,
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
    { rwa [insert_eq j B, ←eq, sdiff_union_of_subset subs] } }
end

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
      rw ←subset.antisymm_iff at q,
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
      rw [←nat.sub_add_cancel (card_le_of_subset AsubC),
          nat.add_sub_assoc (card_le_of_subset BsubA), card_CdiffA_is_1,
          card_AdiffB_is_k, add_comm] },
    { rintro ⟨A, hA, hBA, hAB⟩,
      have z : (A \ B).nonempty,
      { rw [←finset.card_pos, hAB],
        exact nat.succ_pos _ },
      rcases z with ⟨i, hi⟩,
      have : i ∈ A, rw mem_sdiff at hi,
      { exact hi.1 },
      have : B ⊆ erase A i,
      { intros t th,
        apply mem_erase_of_ne_of_mem _ (hBA th),
        intro a,
        rw mem_sdiff at hi,
        rw a at th,
        exact hi.2 th },
      refine ⟨erase A i, _, ‹_›, _⟩,
      { rw mem_shadow_iff,
        refine ⟨A, hA, i, ‹_›, rfl⟩ },
      rw [card_sdiff ‹B ⊆ erase A i›,
        card_erase_of_mem ‹i ∈ A›, nat.pred_sub,
        ←card_sdiff hBA, hAB],
      simp } }
end

/-- Everything in the `k`-th shadow is `k` smaller than things in the original. -/
lemma sized.shadow_iter (h𝒜 : sized 𝒜 r) : sized (shadow^[k] 𝒜) (r-k) :=
begin
  intro B,
  rw sub_iff_shadow_iter,
  rintro ⟨A, hA, hBA, card⟩,
  rw [card_sdiff hBA, h𝒜 hA] at card,
  rw [←card, ←h𝒜 hA, nat.sub_sub_self (card_le_of_subset hBA)],
end

end finset
