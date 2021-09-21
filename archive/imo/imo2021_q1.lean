/-
Copyright (c) 2021 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/

import data.real.sqrt
import tactic.interval_cases
import tactic.linarith
import tactic.norm_cast
import tactic.norm_num
import tactic.ring_exp


/-!
# IMO 2021 Q1

Let `n≥100` be an integer. Ivan writes the numbers` n, n+1,..., 2n` each on different cards.
He then shuffles these `n+1` cards, and divides them into two piles. Prove that at least one
of the piles contains two cards such that the sum of their numbers is a perfect square.

# Solution

We show there exists a triplet `a, b, c ∈ [n , 2n]` with `a < b < c` and each of the sums `(a + b)`,
`(b + c)`, `(a + c)` being a perfect square. Specifically, we consider the linear system of
equations

    a + b = (2 * l - 1) ^ 2
    a + c = (2 * l) ^ 2
    b + c = (2 * l + 1) ^ 2

which can be solved to give

    a = 2 * l * l - 4 * l
    b = 2 * l * l + 1
    c = 2 * l * l + 4 * l

Therefore, it is enough to show that there exists a natural number l such that
`n ≤ 2 * l * l - 4 * l` and `2 * l * l + 4 * l ≤ 2 * n` for `n ≥ 100`.

Then, by the Pigeonhole principle, at least two numbers in the triplet must lie in the same pile,
which finishes the proof.
-/

open real

lemma lower_bound (n l : ℕ) (hl : 2 + sqrt (4 + 2 * n) ≤ 2 * l) :
  n + 4 * l ≤ 2 * l * l :=
begin
  have h₁ : sqrt (4 + 2 * n) ≤ 2 * l - 2 := le_sub_iff_add_le'.mpr hl,
  replace h₁ := (sqrt_le_iff.1 h₁).2,
  ring_exp at h₁,
  norm_num at h₁,
  norm_cast at h₁,
  linarith,
end

lemma upper_bound (n l : ℕ) (hl₂ : (l : ℝ) ≤ sqrt (1 + n) - 1) :
  2 * l * l + 4 * l ≤ 2 * n :=
begin
  have h₁ : (l : ℝ) + 1 ≤ sqrt (1 + n) := le_sub_iff_add_le.mp hl₂,
  rw le_sqrt at h₁,
  ring_exp at h₁, norm_num at h₁,
  norm_cast at h₁,
  linarith,
  all_goals { norm_cast, linarith },
end


lemma radical_inequality {n : ℕ} (h : 107 ≤ n) : sqrt (4 + 2 * n) ≤ 2 * (sqrt (1 + n) - 3) :=
begin
  rw sqrt_le_iff,
  split,
  { norm_num,
    rw le_sqrt,
    all_goals { norm_cast, linarith } },
  { ring_exp,
    rw [pow_two, ← sqrt_mul, sqrt_mul_self],
    suffices : 24 * sqrt (1 + n) ≤ 2 * n + 36,
    { linarith },
    rw mul_self_le_mul_self_iff,
    ring_exp,
    rw [pow_two, ← sqrt_mul, sqrt_mul_self],
    -- Not splitting into cases lead to a deterministic timeout on my machine
    by_cases p: n ≥ 108,
    { norm_cast,
      nlinarith },
    { simp only [not_le] at p,
      have : n = 107 := nat.eq_of_le_of_lt_succ h p,
      subst this,
      norm_num },
    swap 3,
    { norm_num,
      apply sqrt_nonneg },
      all_goals { norm_cast, linarith } },
end

-- We will later make use of the fact that there exists (l : ℕ) such that
-- n ≤ 2 * l * l - 4 * l and 2 * l * l + 4 * l ≤ 2 * n for n ≥ 107.
lemma exists_numbers_in_interval (n : ℕ) (hn : 107 ≤ n) :
  ∃ (l : ℕ), (n + 4 * l ≤ 2 * l * l ∧ 2 * l * l + 4 * l ≤ 2 * n) :=
begin
  suffices : ∃ (l : ℕ), 2 + sqrt (4 + 2 * n) ≤ 2 * (l : ℝ) ∧ (l : ℝ) ≤ sqrt (1 + n) - 1,
  { cases this with l t,
    use l,
    exact ⟨lower_bound n l t.1, upper_bound n l t.2⟩ },
  lift floor (sqrt (1 + n) - 1) to ℕ with x,
  have hx : (x : ℝ) = ⌊sqrt (1 + ↑n) - 1⌋,
  { norm_cast,
    convert h,
    push_cast,
    norm_num },
  refine ⟨x, _, _⟩,
  { suffices : 2 + sqrt (4 + 2 * n) ≤ 2 * (sqrt (1 + n) - 2),
    { apply this.trans _,
      simp only [mul_le_mul_left, zero_lt_bit0, zero_lt_one],
      rw hx,
      suffices : sqrt (1 + n) - 1 ≤ ⌊sqrt (1 + n) - 1⌋ + 1,
      { linarith },
      have t :  (⌈sqrt (1 + n) - 1⌉:ℝ) ≤ ⌊sqrt (1 + n) - 1⌋ + 1,
      { norm_cast,
        exact ceil_le_floor_add_one _ },
      apply le_trans _ t,
      exact le_ceil (sqrt (1 + n) - 1) },
      suffices : sqrt (4 + 2 * n) ≤ 2 * (sqrt (1 + n) - 3),
      { linarith },
    exact radical_inequality hn },
  { rw hx,
    exact floor_le _ },
  { rw [floor_nonneg, le_sub, sub_zero, le_sqrt];
    { norm_cast, linarith } },
end

lemma exists_triplet_summing_to_squares (n : ℕ) (hn : 100 ≤ n) :
  (∃ (a b c : ℕ), n ≤ a ∧ a < b ∧ b < c ∧ c ≤ 2 * n ∧ (∃ (k : ℕ), a + b = k * k) ∧
  (∃ (l : ℕ), c + a = l * l) ∧ (∃ (m : ℕ), b + c = m * m)) :=
begin
  -- If n ≥ 107, we do not explicitly construct the triplet but use an existence
  -- argument from lemma above.
  by_cases p : 107 ≤ n,
  { have h := exists_numbers_in_interval n p,
    cases h with l hl,
    by_cases p : 1 < l,
    { have h₁ : 4 * l ≤ 2 * l * l, { linarith },
      have h₂ : 1 ≤ 2 * l, { linarith },
      refine ⟨2 * l * l - 4 * l, 2 * l * l + 1, 2 * l * l + 4 * l,
      _,_,_,⟨_,⟨2 * l - 1, _⟩,⟨2 * l, _⟩,2 * l + 1, _⟩⟩,
      all_goals { zify [h₁, h₂], linarith } },
    { exfalso,
      simp only [not_lt] at p,
      interval_cases l; linarith }},
  -- Otherwise, if 100 ≤ n < 107, then it suffices to consider explicit
  -- construction of a triplet {a, b, c}, which is constructed by setting l=9
  -- in the argument at the start of the file.
  { refine ⟨126, 163, 198, _, _, _, _,⟨17, _⟩, ⟨18, _⟩, 19, _⟩; linarith },
end

-- Since it will be more convenient to work with sets later on, we will translate the above claim
-- to state that there always exists a set B ⊆ [n, 2n] of cardinality at least 3, such that each
-- pair of pairwise unequal elements of B sums to a perfect square.
lemma exists_finset_of_3_leq_card_with_pairs_summing_to_squares (n : ℕ) (hn : 100 ≤ n) :
  ∃ (B : finset ℕ), 2 * 1 + 1 ≤ B.card ∧
  (∀ (a b ∈ B), a ≠ b → ∃ k, a + b = k * k) ∧
  ∀ (c ∈ B), n ≤ c ∧ c ≤ 2 * n :=
begin
  obtain ⟨a, b, c, hna, hab, hbc, hcn, h₁, h₂, h₃⟩ := exists_triplet_summing_to_squares n hn,
  refine ⟨{a, b, c}, _, _, _⟩,
  { suffices : ({a, b, c} : finset ℕ).card = 3,
    { linarith },
    rw [finset.card_insert_of_not_mem, finset.card_insert_of_not_mem, finset.card_singleton],
    { rw finset.mem_singleton,
      exact hbc.ne },
    { simp only [finset.mem_insert, finset.mem_singleton],
      push_neg,
      exact ⟨hab.ne, (hab.trans hbc).ne⟩ }},
  { intros x y hx hy hxy,
    simp only [finset.mem_insert, finset.mem_singleton] at hx,
    simp only [finset.mem_insert, finset.mem_singleton] at hy,
    rcases hx with (hxa | hxb | hxc),
    { rcases hy with (hya | hyb | hyc),
      { rw ← hya at hxa,
        contradiction },
      { convert h₁,
        rw [hxa, hyb] },
      { convert h₂,
        rw [hxa, hyc, add_comm] }},
    { rcases hy with (hya | hyb | hyc),
      { convert h₁,
        rw [hxb, hya, add_comm] },
      { rw ← hyb at hxb,
        contradiction },
      { convert h₃,
        rw [hxb, hyc] }},
    { rcases hy with (hya | hyb | hyc),
      { convert h₂,
        rw [hxc, hya] },
      { convert h₃,
        rw [hxc, hyb, add_comm] },
      { rw ← hyc at hxc,
        contradiction }}},
  { intros d hd,
    simp only [finset.mem_insert, finset.mem_singleton] at hd,
    split,
    { rcases hd with (hd | hd | hd);
      { linarith }},
    { rcases hd with (hd | hd | hd);
      { linarith }}},
end

-- If for n ∈ ℕ, and finite sets B, X, Y such that B ⊆ X ∪ Y and B has cardinality at least
-- 2 * n + 1, then there exists a subset C ⊆ A of cardinality at least n + 1, which is entirely
-- contained in X or Y. For our result, we will apply this lemma with n = 1 and any X such that
-- X ⊆ [n, 2n] and Y = [n, 2n] \ X, while we'll let B ⊆ [n, 2n] be the subset such that each
-- pairwise unequal pair of B sums to a perfect square.
lemma finset_subset_or_complement_cardinality {α : Type*} [decidable_eq α] (B X Y : finset α)
  (h : B ⊆ X ∪ Y) {n : ℕ} (hB : 2 * n + 1 ≤ B.card) :
  (∃ C, C ⊆ B ∧ C ⊆ X ∧ n + 1 ≤ C.card) ∨ (∃ C, C ⊆ B ∧ C ⊆ Y ∧ n + 1 ≤ C.card) :=
begin
  by_contra h,
  push_neg at h,
  cases h with h₁ h₂,
  have h₃ : B \ (Y \ X) ⊆ B := finset.sdiff_subset B (Y \ X),
  have h₄ : B \ (Y \ X) ⊆ X,
  { refine ((finset.sdiff_subset_sdiff h (finset.subset.refl (Y \ X))).trans (λ i hi, _)),
    simp only [not_and, not_not, finset.mem_sdiff, finset.mem_union] at hi,
    cases hi with hi₁ hi₂,
    cases hi₁,
    { exact hi₁ },
    { exact hi₂ hi₁ }},
  have h₅ : B \ (X \ Y) ⊆ B := finset.sdiff_subset B (X \ Y),
  have h₆ : B \ (X \ Y) ⊆ Y,
  { refine ((finset.sdiff_subset_sdiff h (finset.subset.refl (X \ Y))).trans (λ i hi, _)),
    simp only [not_and, not_not, finset.mem_sdiff, finset.mem_union] at hi,
    cases hi with hi₁ hi₂,
    cases hi₁,
    { exact hi₂ hi₁ },
    { exact hi₁ }},
  specialize h₁ (B \ (Y \ X)) h₃ h₄,
  specialize h₂ (B \ (X \ Y)) h₅ h₆,
  have h₇ : B ⊆ B \ (Y \ X) ∪ B \ (X \ Y),
  { intros i hi,
    simp only [not_and, not_not, finset.mem_sdiff, finset.mem_union],
    have h₈ : i ∈ X ∨ i ∈ Y := finset.mem_union.mp (h hi),
    cases h₈,
    { left,
      exact ⟨hi, (λ x, h₈)⟩ },
    { right,
      exact ⟨hi,(λ x, h₈)⟩ }},
  replace h₇ := finset.card_le_of_subset h₇,
  have h₉ : B.card ≤  2 * n,
  { apply le_trans h₇ _,
    apply le_trans ((B \ (Y \ X)).card_union_le (B \ (X \ Y))) _,
    linarith },
  linarith,
end

lemma finset_two_le_card_exists_pair_neq (C : finset ℕ) (hC : 2 ≤ C.card) :
  ∃ (a b ∈ C), a ≠ b :=
begin
  by_contra hab,
  push_neg at hab,
  rw ← finset.card_le_one_iff at hab,
  linarith,
end


theorem IMO_2021_Q1 : ∀ (n : ℕ), 100 ≤ n → ∀ (A ⊆ finset.Ico n (2 * n + 1)),
  (∃ (a b ∈ A), a ≠ b ∧ ∃ (k : ℕ), a + b = k * k) ∨
  (∃ (a b ∈ finset.Ico n (2 * n + 1) \ A), a ≠ b ∧ ∃ (k : ℕ), a + b = k * k) :=
begin
  intros n hn A hA,
  -- For each n ∈ ℕ such that 100 ≤ n, there exists a pairwise unequal triplet {a, b, c} ⊆ [n, 2n]
  -- such that all pairwise sums are perfect squares. In practice, it will be easier to use
  -- a finite set B ⊆ [n, 2n] such that all pairwise unequal pairs of B sum to a perfect square
  -- noting that B has cardinality greater or equal to 3, by the explicit construction of the
  -- triplet {a, b, c} before.
  obtain ⟨B, hB, h₁, h₂⟩ := exists_finset_of_3_leq_card_with_pairs_summing_to_squares n hn,
  have hBA : B ⊆ (finset.Ico n (2 * n + 1) \ A) ∪ A,
  { rw finset.sdiff_union_of_subset hA,
    intros c hc,
    simp only [finset.Ico.mem],
    refine ⟨(h₂ c hc).1, _⟩,
    { replace h₂ := (h₂ c hc).2,
      exact nat.lt_succ_iff.mpr h₂ }},
  -- Since B has cardinality greater or equal to 3, there must exist a subset C ⊆ B such that
  -- for any A ⊆ [n, 2n], either C ⊆ A or C ⊆ [n, 2n] \ A and C has cardinality greater
  -- or equal to 2.
  have hp₂ := finset_subset_or_complement_cardinality B (finset.Ico n (2 * n + 1) \ A) A hBA hB,
  rcases hp₂ with (⟨C, hCB, hCA, hC⟩ | ⟨C, hCB, hCA, hC⟩),
  -- First, we deal with the case when C ⊆ [n, 2n] \ A.
  { right,
    norm_num at hC,
    have hab := finset_two_le_card_exists_pair_neq C hC,
    rcases hab with ⟨a, b, ha, hb, hab⟩,
    exact ⟨a, b, hCA ha, hCA hb, hab, h₁ a b (hCB ha) (hCB hb) hab⟩ },
  -- Then, we finish the proof in the case when C ⊆ A.
  { left,
    norm_num at hC,
    have hab := finset_two_le_card_exists_pair_neq C hC,
    rcases hab with ⟨a, b, ha, hb, hab⟩,
    exact ⟨a, b, hCA ha, hCA hb, hab, h₁ a b (hCB ha) (hCB hb) hab⟩ },
end
