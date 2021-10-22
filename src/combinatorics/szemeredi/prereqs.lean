/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib

/-!
# Prerequisites for SRL
-/

open_locale big_operators
open finset fintype function relation

variables {α : Type*}

section relation
variables (r : α → α → Prop) [decidable_rel r]

lemma lemma_B_ineq_zero {s t : finset α} (hst : s ⊆ t) (f : α → ℝ) {x : ℝ}
  (hs : x^2 ≤ ((∑ x in s, f x)/s.card)^2) :
  (s.card : ℝ) * x^2 ≤ ∑ x in t, f x^2 :=
begin
  refine (mul_le_mul_of_nonneg_left (hs.trans (chebyshev s f)) (nat.cast_nonneg _)).trans _,
  refine le_trans _ (sum_le_sum_of_subset_of_nonneg hst (λ i _ _, sq_nonneg _)),
  refine (mul_div_cancel_of_imp' _).le,
  simp only [finset.card_eq_zero, nat.cast_eq_zero],
  rintro rfl,
  simp
end

lemma lemma_B_ineq {s t : finset α} (hst : s ⊆ t) (f : α → ℝ) (d : ℝ) {x : ℝ} (hx : 0 ≤ x)
  (hs : x ≤ abs ((∑ i in s, f i)/s.card - (∑ i in t, f i)/t.card))
  (ht : d ≤ ((∑ i in t, f i)/t.card)^2) :
  d + s.card/t.card * x^2 ≤ (∑ i in t, f i^2)/t.card :=
begin
  obtain hscard | hscard := (s.card.cast_nonneg : (0 : ℝ) ≤ s.card).eq_or_lt,
  { rw [←hscard, zero_div, zero_mul, add_zero],
    apply ht.trans (chebyshev _ _) },
  have htcard : (0:ℝ) < t.card := hscard.trans_le (nat.cast_le.2 (card_le_of_subset hst)),
  have h₁ : x^2 ≤ ((∑ i in s, f i)/s.card - (∑ i in t, f i)/t.card)^2 :=
    sq_le_sq (by rwa [abs_of_nonneg hx]),
  have h₂ : x^2 ≤ ((∑ i in s, (f i - (∑ j in t, f j)/t.card))/s.card)^2,
  { apply h₁.trans,
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, sub_div, mul_div_cancel_left _ hscard.ne'] },
  apply (add_le_add_right ht _).trans,
  rw [←mul_div_right_comm, le_div_iff htcard, add_mul, div_mul_cancel _ htcard.ne'],
  have h₃ := lemma_B_ineq_zero hst (λ i, f i - (∑ j in t, f j) / t.card) h₂,
  apply (add_le_add_left h₃ _).trans,
  simp [←mul_div_right_comm _ (t.card : ℝ), sub_div' _ _ _ htcard.ne', ←sum_div, ←add_div, mul_pow,
    div_le_iff (sq_pos_of_ne_zero _ htcard.ne'), sub_sq, sum_add_distrib, ←sum_mul, ←mul_sum],
  ring_nf,
end

lemma aux₀ {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) :
 (A'.card : ℝ)/A.card * (B'.card/B.card) * pairs_density r A' B' ≤ pairs_density r A B :=
begin
  obtain hA' | hA' := nat.eq_zero_or_pos A'.card,
  { rw [hA', nat.cast_zero, zero_div, zero_mul, zero_mul],
    exact pairs_density_nonneg r A B },
  obtain hB' | hB' := nat.eq_zero_or_pos B'.card,
  { rw [hB', nat.cast_zero, zero_div, mul_zero, zero_mul],
    exact pairs_density_nonneg r A B },
  have hAB' : (0 : ℝ) < A'.card * B'.card := by exact_mod_cast mul_pos hA' hB',
  have hAB : (0 : ℝ) < A.card * B.card := hAB'.trans_le
    (by exact_mod_cast nat.mul_le_mul (card_le_of_subset hA) (card_le_of_subset hB)),
  rw [pairs_density, pairs_density, div_mul_div, mul_comm, div_mul_div_cancel _ hAB'.ne',
    div_le_div_right hAB, nat.cast_le],
  exact card_le_of_subset (pairs_finset_mono r hA hB),
end

lemma aux₁ {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) :
  pairs_density r A' B' - pairs_density r A B ≤ 1 - (A'.card : ℝ)/A.card * (B'.card/B.card) :=
begin
  refine (sub_le_sub_left (aux₀ r hA hB) _).trans _,
  refine le_trans _ (mul_le_of_le_one_right _ (pairs_density_le_one r A' B')),
  { rw [sub_mul, one_mul] },
  refine sub_nonneg_of_le (mul_le_one _ (div_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)) _);
  exact div_le_one_of_le (nat.cast_le.2 (card_le_of_subset ‹_›)) (nat.cast_nonneg _),
end

lemma aux₂ {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) :
  abs (pairs_density r A' B' - pairs_density r A B) ≤ 1 - (A'.card : ℝ)/A.card * (B'.card/B.card) :=
begin
  have habs : abs (pairs_density r A' B' - pairs_density r A B) ≤ 1,
  { rw [abs_sub_le_iff, ←sub_zero (1 : ℝ)],
    split; exact sub_le_sub (pairs_density_le_one r _ _) (pairs_density_nonneg r _ _) },
  obtain rfl | hA' := A'.eq_empty_or_nonempty,
  { rwa [finset.card_empty, nat.cast_zero, zero_div, zero_mul, sub_zero] },
  obtain rfl | hB' := B'.eq_empty_or_nonempty,
  { rwa [finset.card_empty, nat.cast_zero, zero_div, mul_zero, sub_zero] },
  refine abs_sub_le_iff.2 ⟨aux₁ r hA hB, _⟩,
  rw [←add_sub_cancel (pairs_density r A B) (pairs_density (λ x y, ¬r x y) A B),
    ←add_sub_cancel (pairs_density r A' B') (pairs_density (λ x y, ¬r x y) A' B'),
    pairs_density_compl _ (hA'.mono hA) (hB'.mono hB), pairs_density_compl _ hA' hB',
    sub_sub_sub_cancel_left],
  exact aux₁ _ hA hB,
end

lemma aux₃ {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
  (hAcard : (1 - δ) * A.card ≤ A'.card) (hBcard : (1 - δ) * B.card ≤ B'.card) :
  abs (pairs_density r A' B' - pairs_density r A B) ≤ 2*δ - δ^2 :=
begin
  have hδ' : 0 ≤ 2 * δ - δ ^ 2,
  { rw [sub_nonneg, sq],
    exact mul_le_mul_of_nonneg_right (hδ₁.le.trans (by norm_num)) hδ₀ },
  rw ←sub_pos at hδ₁,
  obtain hA' | hA'pos := (nat.cast_nonneg A'.card).eq_or_lt,
  { rw ←hA' at hAcard,
    rwa [pairs_density, pairs_density, ←hA', (nonpos_of_mul_nonpos_left hAcard hδ₁).antisymm
      (nat.cast_nonneg _), zero_mul, zero_mul, div_zero, div_zero, sub_zero, abs_zero] },
  obtain hB' | hB'pos := (nat.cast_nonneg B'.card).eq_or_lt,
  { rw ←hB' at hBcard,
    rwa [pairs_density, pairs_density, ←hB', (nonpos_of_mul_nonpos_left hBcard hδ₁).antisymm
      (nat.cast_nonneg _), mul_zero, mul_zero, div_zero, div_zero, sub_zero, abs_zero] },
  have hApos : (0 : ℝ) < A.card := hA'pos.trans_le (nat.cast_le.2 (card_le_of_subset hA)),
  have hBpos : (0 : ℝ) < B.card := hB'pos.trans_le (nat.cast_le.2 (card_le_of_subset hB)),
  apply (aux₂ r hA hB).trans,
  apply (sub_le_sub_left (mul_le_mul ((le_div_iff hApos).2 hAcard) _ hδ₁.le _) _).trans,
  { exact le_of_eq (by ring) },
  { rwa le_div_iff hBpos },
  { refine div_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _) },
end

/-- Lemma A: if A' ⊆ A, B' ⊆ B each take up all but a δ-proportion, then the difference in edge
densities is `≤ 2 δ`. -/
lemma lemma_A {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) {δ : ℝ} (hδ : 0 ≤ δ)
  (hAcard : (1 - δ) * A.card ≤ A'.card) (hBcard : (1 - δ) * B.card ≤ B'.card) :
  abs (pairs_density r A' B' - pairs_density r A B) ≤ 2 * δ :=
begin
  cases lt_or_le δ 1,
  { exact (aux₃ r hA hB hδ h hAcard hBcard).trans ((sub_le_self_iff _).2 (sq_nonneg δ)) },
  refine (abs_sub _ _).trans _,
  simp only [abs_of_nonneg (pairs_density_nonneg r _ _), two_mul],
  exact add_le_add ((pairs_density_le_one r _ _).trans h) ((pairs_density_le_one r A B).trans h),
end

end relation
