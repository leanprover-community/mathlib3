/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib
import combinatorics.choose.bounds
import data.sym.card

open_locale big_operators
open finset fintype function relation

variables {α : Type*}

namespace finset
variable [decidable_pred (λ (ab : α × α), well_ordering_rel ab.fst ab.snd)]

/-- Pairs of parts. We exclude the diagonal, as these do not make sense nor
behave well in the context of Szemerédi's Regularity Lemma. -/
def distinct_pairs (s : finset α) :
  finset (α × α) :=
(s.product s).filter (λ ab, well_ordering_rel ab.1 ab.2)

variable {s : finset α}

lemma mem_distinct_pairs (a b : α) :
  (a, b) ∈ s.distinct_pairs ↔ a ∈ s ∧ b ∈ s ∧ well_ordering_rel a b :=
by rw [distinct_pairs, mem_filter, mem_product, and_assoc]

lemma distinct_pairs_subset_off_diag [decidable_eq α] : s.distinct_pairs ⊆ s.off_diag :=
begin
  rintro ⟨x₁, x₂⟩,
  simp only [mem_distinct_pairs, and_imp, mem_off_diag],
  rintro h₁ h₂ h,
  exact ⟨h₁, h₂, ne_of_irrefl h⟩,
end

lemma distinct_pairs_card [decidable_eq α] :
  s.distinct_pairs.card = s.card.choose 2 :=
begin
  rw ←sym2.card_image_off_diag,
  refine card_congr (λ a _, ⟦a⟧) _ _ _,
  { rintro ⟨a₁, a₂⟩ ha,
    apply mem_image_of_mem _ (distinct_pairs_subset_off_diag ha) },
  { rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩,
    simp only [prod.mk.inj_iff, mem_distinct_pairs, and_imp, sym2.eq_iff],
    rintro _ _ h₁ _ _ h₂ (i | ⟨rfl, rfl⟩),
    { exact i },
    cases asymm h₁ h₂ },
  { refine quotient.ind _,
    simp only [mem_image, forall_exists_index, sym2.eq_iff, prod.forall, exists_prop, mem_off_diag,
      mem_distinct_pairs, prod.exists, and_assoc, and_imp],
    rintro a b x y _ _ dif h,
    obtain ⟨ha, hb⟩ : a ∈ s ∧ b ∈ s,
    { rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩);
      exact ⟨‹_›, ‹_›⟩ },
    rcases trichotomous_of well_ordering_rel a b with lt | rfl | gt,
    { exact ⟨_, _, ‹a ∈ s›, ‹b ∈ s›, lt, by simp⟩ },
    { simp only [or_self] at h,
      cases dif (h.1.trans h.2.symm) },
    { exact ⟨_, _, ‹b ∈ s›, ‹a ∈ s›, gt, by simp⟩ } },
end

end finset

open finset

namespace finpartition_on
variables {s : finset α} (P : finpartition_on s) (G : simple_graph α)
open_locale classical

/-- The index is the auxiliary quantity that drives the induction process in the proof of
Szemerédi's Regularity Lemma (see `increment`). As long as we do not have a suitable equipartition,
we will find a new one that has an index greater than the previous one plus some fixed constant.
Then `index_le_half` ensures this process only happens finitely many times. -/
noncomputable def index (P : finpartition_on s) : ℝ :=
(∑ UV in P.parts.distinct_pairs, G.edge_density UV.1 UV.2^2)/P.size^2

lemma index_nonneg (P : finpartition_on s) :
  0 ≤ P.index G :=
div_nonneg (finset.sum_nonneg (λ _ _, sq_nonneg _)) (sq_nonneg _)

lemma index_le_half (P : finpartition_on s) :
  P.index G ≤ 1/2 :=
begin
  rw finpartition_on.index,
  apply div_le_of_nonneg_of_le_mul (sq_nonneg _),
  { norm_num },
  suffices h : (∑ UV in P.parts.distinct_pairs, G.edge_density UV.1 UV.2^2) ≤
    P.parts.distinct_pairs.card,
  { apply h.trans,
    rw [distinct_pairs_card, div_mul_eq_mul_div, one_mul],
    convert choose_le_pow 2 _,
    norm_num },
  rw [finset.card_eq_sum_ones, nat.cast_sum, nat.cast_one],
  refine finset.sum_le_sum (λ s _, _),
  rw [sq, ←abs_le_one_iff_mul_self_le_one, abs_eq_self.2 (G.edge_density_nonneg _ _)],
  exact G.edge_density_le_one _ _,
end

end finpartition_on
