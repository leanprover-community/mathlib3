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

lemma lemma_B {s t : finset α} (hst : s ⊆ t) (f : α → ℝ) {a b : ℝ}
  (hs : (∑ x in s, f x)/s.card = a + b) (ht : (∑ x in t, f x) / t.card = a) :
  a^2 + s.card/t.card * b^2 ≤ (∑ x in t, f x^2)/t.card :=
begin
  obtain htcard | htcard := (t.card.cast_nonneg : (0 : ℝ) ≤ t.card).eq_or_lt,
  { rw [←ht, ←htcard, div_zero, div_zero, div_zero, zero_mul, add_zero, pow_succ, zero_mul] },
  obtain hscard | hscard := (s.card.cast_nonneg : (0 : ℝ) ≤ s.card).eq_or_lt,
  { rw [←hscard, zero_div, zero_mul, add_zero, ←ht, le_div_iff htcard, div_pow, sq (t.card : ℝ),
      div_mul_eq_mul_div_comm, div_self_mul_self', mul_inv_le_iff htcard],
    simpa using sum_mul_sq_le_sq_mul_sq t (λ _, 1) f },
  have htzero : (t.card : ℝ) ≠ 0 := htcard.ne',
  have hszero : (s.card : ℝ) ≠ 0 := hscard.ne',
  rw div_eq_iff htzero at ht,
  rw div_eq_iff hszero at hs,
  suffices h : (∑ x in s, (f x - a))^2 ≤ s.card * (∑ x in t, (f x - a)^2),
  { apply le_of_mul_le_mul_left _ htcard,
    rw [mul_add, ←mul_assoc, mul_div_cancel' _ htzero, mul_div_cancel' _ htzero,
      ←le_sub_iff_add_le'],
    apply le_of_mul_le_mul_left _ hscard,
    rw [←mul_assoc, ←sq],
    simp_rw sub_sq at h,
    rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ←sum_mul, ←mul_sum, sum_const,
      sum_const, ht, hs, nsmul_eq_mul, nsmul_eq_mul, mul_comm (a + b), ←mul_sub, add_sub_cancel',
    mul_pow] at h,
    convert h,
    ring },
  have cs := sum_mul_sq_le_sq_mul_sq s (λ _, 1) (λ x, f x - a),
  simp only [one_pow, one_mul, nsmul_eq_mul, sum_const, nat.smul_one_eq_coe] at cs,
  apply cs.trans _,
  rw mul_le_mul_left hscard,
  exact sum_le_sum_of_subset_of_nonneg hst (λ i _ _, sq_nonneg _),
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
  have hAB : (0 : ℝ) < A.card * B.card := by exact_mod_cast mul_pos (hA'.trans_le
    (finset.card_le_of_subset hA)) (hB'.trans_le (finset.card_le_of_subset hB)),
  rw [pairs_density, pairs_density, div_mul_div, mul_comm, div_mul_div_cancel _ hAB'.ne',
    div_le_div_right hAB, nat.cast_le],
  exact finset.card_le_of_subset (pairs_finset_mono r hA hB),
end

lemma aux₁ {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) :
  pairs_density r A' B' - pairs_density r A B ≤ 1 - (A'.card : ℝ)/A.card * (B'.card/B.card) :=
calc
  pairs_density r A' B' - pairs_density r A B
      ≤ pairs_density r A' B' - A'.card/A.card * (B'.card/B.card) * pairs_density r A' B'
      : sub_le_sub_left (aux₀ r hA hB) _
  ... = (1 - A'.card/A.card * (B'.card/B.card)) * pairs_density r A' B'
      : by rw [sub_mul, one_mul]
  ... ≤ 1 - A'.card/A.card * (B'.card/B.card)
      : begin
          refine mul_le_of_le_one_right (sub_nonneg_of_le $ mul_le_one _ _ _)
            (pairs_density_le_one r _ _),
          exact div_le_one_of_le (nat.cast_le.2 (finset.card_le_of_subset hA)) (nat.cast_nonneg _),
          exact div_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _),
          exact div_le_one_of_le (nat.cast_le.2 (finset.card_le_of_subset hB)) (nat.cast_nonneg _),
        end

variable [decidable_eq α]

lemma aux₂ {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) :
  abs (pairs_density r A' B' - pairs_density r A B) ≤ 1 - (A'.card : ℝ)/A.card * (B'.card/B.card) :=
begin
  have habs : abs (pairs_density r A' B' - pairs_density r A B) ≤ 1,
  { rw [abs_sub_le_iff, ←sub_zero (1 : ℝ)],
    split; exact sub_le_sub (pairs_density_le_one r _ _) (pairs_density_nonneg r _ _) },
  obtain hA' | hA' := nat.eq_zero_or_pos A'.card,
  { rw [hA', nat.cast_zero, zero_div, zero_mul, sub_zero],
    exact habs },
  obtain hB' | hB' := nat.eq_zero_or_pos B'.card,
  { rw [hB', nat.cast_zero, zero_div, mul_zero, sub_zero],
    exact habs },
  rw finset.card_pos at hA' hB',
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
    refine mul_le_mul_of_nonneg_right (hδ₁.le.trans _) hδ₀,
    norm_num },
  rw ←sub_pos at hδ₁,
  obtain hA' | hA'pos := (nat.cast_nonneg A'.card).eq_or_lt,
  { rw ←hA' at hAcard,
    rwa [pairs_density, pairs_density, ←hA', (nonpos_of_mul_nonpos_left hAcard hδ₁).antisymm
      (nat.cast_nonneg _), zero_mul, zero_mul, div_zero, div_zero, sub_zero, abs_zero] },
  obtain hB' | hB'pos := (nat.cast_nonneg B'.card).eq_or_lt,
  { rw ←hB' at hBcard,
    rwa [pairs_density, pairs_density, ←hB', (nonpos_of_mul_nonpos_left hBcard hδ₁).antisymm
      (nat.cast_nonneg _), mul_zero, mul_zero, div_zero, div_zero, sub_zero, abs_zero] },
  have hApos : (0 : ℝ) < A.card := hA'pos.trans_le (nat.cast_le.2 (finset.card_le_of_subset hA)),
  have hBpos : (0 : ℝ) < B.card := hB'pos.trans_le (nat.cast_le.2 (finset.card_le_of_subset hB)),
  calc
    abs (pairs_density r A' B' - pairs_density r A B)
        ≤ 1 - A'.card/A.card * (B'.card/B.card)
        : aux₂ r hA hB
    ... ≤ 1 - (1 - δ) * (1 - δ)
        : sub_le_sub_left (mul_le_mul ((le_div_iff hApos).2 hAcard) ((le_div_iff hBpos).2
            hBcard) hδ₁.le (div_nonneg hA'pos.le hApos.le)) 1
    ... = 2*δ - δ^2
        : by ring,
end

/-- Lemma A: if A' ⊆ A, B' ⊆ B each take up all but a δ-proportion, then the difference in edge
densities is `≤ 2 δ`. -/
lemma lemma_A {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) {δ : ℝ} (hδ : 0 ≤ δ)
  (hAcard : (1 - δ) * A.card ≤ A'.card) (hBcard : (1 - δ) * B.card ≤ B'.card) :
  abs (pairs_density r A' B' - pairs_density r A B) ≤ 2 * δ :=
begin
  cases le_or_lt 1 δ,
  { refine (abs_sub _ _).trans _,
    rw [abs_of_nonneg (pairs_density_nonneg r _ _), abs_of_nonneg (pairs_density_nonneg r A B),
      two_mul],
    exact add_le_add ((pairs_density_le_one r _ _).trans h)
      ((pairs_density_le_one r A B).trans h) },
  exact (aux₃ r hA hB hδ h hAcard hBcard).trans ((sub_le_self_iff _).2 (sq_nonneg δ)),
end

end relation
