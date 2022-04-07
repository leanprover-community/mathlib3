/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib

/-!
# Prerequisites for SRL
-/

open_locale big_operators
open finset fintype function rel

variables {α : Type*}

section relation
variables (r : α → α → Prop) [decidable_rel r] {A B A' B' : finset α}

lemma lemma_B_ineq_zero {s t : finset α} (hst : s ⊆ t) (f : α → ℝ) {x : ℝ}
  (hs : x^2 ≤ ((∑ x in s, f x)/s.card)^2) (hs' : (s.card : ℝ) ≠ 0) :
  (s.card : ℝ) * x^2 ≤ ∑ x in t, f x^2 :=
(mul_le_mul_of_nonneg_left (hs.trans (chebyshev s f)) (nat.cast_nonneg _)).trans $
  (mul_div_cancel' _ hs').le.trans $ sum_le_sum_of_subset_of_nonneg hst $ λ i _ _, sq_nonneg _

lemma lemma_B_ineq {s t : finset α} (hst : s ⊆ t) (f : α → ℝ) (d : ℝ) {x : ℝ} (hx : 0 ≤ x)
  (hs : x ≤ abs ((∑ i in s, f i)/s.card - (∑ i in t, f i)/t.card))
  (ht : d ≤ ((∑ i in t, f i)/t.card)^2) :
  d + s.card/t.card * x^2 ≤ (∑ i in t, f i^2)/t.card :=
begin
  obtain hscard | hscard := (s.card.cast_nonneg : (0 : ℝ) ≤ s.card).eq_or_lt,
  { simpa [←hscard] using ht.trans (chebyshev t f) },
  have htcard : (0:ℝ) < t.card := hscard.trans_le (nat.cast_le.2 (card_le_of_subset hst)),
  have h₁ : x^2 ≤ ((∑ i in s, f i)/s.card - (∑ i in t, f i)/t.card)^2 :=
    sq_le_sq (by rwa [abs_of_nonneg hx]),
  have h₂ : x^2 ≤ ((∑ i in s, (f i - (∑ j in t, f j)/t.card))/s.card)^2,
  { apply h₁.trans,
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, sub_div, mul_div_cancel_left _ hscard.ne'] },
  apply (add_le_add_right ht _).trans,
  rw [←mul_div_right_comm, le_div_iff htcard, add_mul, div_mul_cancel _ htcard.ne'],
  have h₃ := lemma_B_ineq_zero hst (λ i, f i - (∑ j in t, f j) / t.card) h₂ hscard.ne',
  apply (add_le_add_left h₃ _).trans,
  simp [←mul_div_right_comm _ (t.card : ℝ), sub_div' _ _ _ htcard.ne', ←sum_div, ←add_div, mul_pow,
    div_le_iff (sq_pos_of_ne_zero _ htcard.ne'), sub_sq, sum_add_distrib, ←sum_mul, ←mul_sum],
  ring_nf,
end

lemma aux₀ (hA : A' ⊆ A) (hB : B' ⊆ B) (hA' : A'.nonempty) (hB' : B'.nonempty) :
 (A'.card : ℚ)/A.card * (B'.card/B.card) * edge_density r A' B' ≤ edge_density r A B :=
begin
  have hAB' : (A'.card : ℚ) * (B'.card) ≠ 0 := by simp [hA'.ne_empty, hB'.ne_empty],
  rw [edge_density, edge_density, div_mul_div_comm₀, mul_comm, div_mul_div_cancel _ hAB'],
  refine div_le_div_of_le (by exact_mod_cast (A.card * B.card).zero_le) _,
  exact_mod_cast card_le_of_subset (interedges_mono hA hB),
end

lemma aux₁ (hA : A' ⊆ A) (hB : B' ⊆ B) (hA' : A'.nonempty) (hB' : B'.nonempty) :
  edge_density r A' B' - edge_density r A B ≤ 1 - (A'.card)/A.card * (B'.card/B.card) :=
begin
  refine (sub_le_sub_left (aux₀ r hA hB hA' hB') _).trans _,
  refine le_trans _ (mul_le_of_le_one_right _ (edge_density_le_one r A' B')),
  { rw [sub_mul, one_mul] },
  refine sub_nonneg_of_le (mul_le_one _ (div_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)) _);
  exact div_le_one_of_le (nat.cast_le.2 (card_le_of_subset ‹_›)) (nat.cast_nonneg _),
end

lemma aux₂ (hA : A' ⊆ A) (hB : B' ⊆ B) (hA' : A'.nonempty) (hB' : B'.nonempty) :
  |edge_density r A' B' - edge_density r A B| ≤ 1 - (A'.card : ℚ)/A.card * (B'.card/B.card) :=
begin
  have habs : abs (edge_density r A' B' - edge_density r A B) ≤ 1,
  { rw [abs_sub_le_iff, ←sub_zero (1 : ℚ)],
    split; exact sub_le_sub (edge_density_le_one r _ _) (edge_density_nonneg r _ _) },
  refine abs_sub_le_iff.2 ⟨aux₁ r hA hB hA' hB', _⟩,
  rw [←add_sub_cancel (edge_density r A B) (edge_density (λ x y, ¬r x y) A B),
    ←add_sub_cancel (edge_density r A' B') (edge_density (λ x y, ¬r x y) A' B'),
    edge_density_add_edge_density_compl _ (hA'.mono hA) (hB'.mono hB),
    edge_density_add_edge_density_compl _ hA' hB', sub_sub_sub_cancel_left],
  exact aux₁ _ hA hB hA' hB',
end

lemma aux₃ (hA : A' ⊆ A) (hB : B' ⊆ B) {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
  (hA' : (1 - δ) * A.card ≤ A'.card) (hB' : (1 - δ) * B.card ≤ B'.card) :
  |(edge_density r A' B' : ℝ) - edge_density r A B | ≤ 2*δ - δ^2 :=
begin
  have hδ' : 0 ≤ 2 * δ - δ ^ 2,
  { rw [sub_nonneg, sq],
    exact mul_le_mul_of_nonneg_right (hδ₁.le.trans (by norm_num)) hδ₀ },
  rw ←sub_pos at hδ₁,
  simp only [edge_density],
  obtain rfl | hA'' := A'.eq_empty_or_nonempty,
  { simpa [(nonpos_of_mul_nonpos_left hA' hδ₁).antisymm (nat.cast_nonneg _)] using hδ' },
  obtain rfl | hB'' := B'.eq_empty_or_nonempty,
  { simpa [(nonpos_of_mul_nonpos_left hB' hδ₁).antisymm (nat.cast_nonneg _)] using hδ' },
  rw [←rat.cast_sub, ←rat.cast_abs, show 2 * δ - δ ^ 2 = 1 - (1 - δ) * (1 - δ), by ring],
  refine (rat.cast_le.2 $ aux₂ r hA hB hA'' hB'').trans _,
  push_cast,
  apply sub_le_sub_left (mul_le_mul ((le_div_iff _).2 hA') ((le_div_iff _).2 hB') hδ₁.le _) _,
  { exact_mod_cast (hA''.mono hA).card_pos },
  { exact_mod_cast (hB''.mono hB).card_pos },
  { exact div_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _) }
end

/-- Lemma A: if A' ⊆ A, B' ⊆ B each take up all but a δ-proportion, then the difference in edge
densities is `≤ 2 δ`. -/
lemma lemma_A (hA : A' ⊆ A) (hB : B' ⊆ B) {δ : ℝ} (hδ : 0 ≤ δ)
  (hAcard : (1 - δ) * A.card ≤ A'.card) (hBcard : (1 - δ) * B.card ≤ B'.card) :
  |(edge_density r A' B' : ℝ) - edge_density r A B| ≤ 2 * δ :=
begin
  cases lt_or_le δ 1,
  { exact (aux₃ r hA hB hδ h hAcard hBcard).trans ((sub_le_self_iff _).2 (sq_nonneg δ)) },
  rw two_mul,
  refine (abs_sub _ _).trans (add_le_add (le_trans _ h) (le_trans _ h));
  { rw abs_of_nonneg,
    exact_mod_cast edge_density_le_one r _ _,
    exact_mod_cast edge_density_nonneg r _ _ }
end

end relation
