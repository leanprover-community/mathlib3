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
  lift int.floor (sqrt (1 + n) - 1) to ℕ with x,
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
        exact int.ceil_le_floor_add_one _ },
      apply le_trans _ t,
      exact int.le_ceil (sqrt (1 + n) - 1) },
      suffices : sqrt (4 + 2 * n) ≤ 2 * (sqrt (1 + n) - 3),
      { linarith },
    exact radical_inequality hn },
  { rw hx,
    exact int.floor_le _ },
  { rw [int.floor_nonneg, le_sub, sub_zero, le_sqrt];
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
  { refine ⟨126, 163, 198, _, _, _, _, ⟨17, _⟩, ⟨18, _⟩, 19, _⟩; linarith },
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

theorem IMO_2021_Q1 : ∀ (n : ℕ), 100 ≤ n → ∀ (A ⊆ finset.Icc n (2 * n)),
  (∃ (a b ∈ A), a ≠ b ∧ ∃ (k : ℕ), a + b = k * k) ∨
  (∃ (a b ∈ finset.Icc n (2 * n) \ A), a ≠ b ∧ ∃ (k : ℕ), a + b = k * k) :=
begin
  intros n hn A hA,
  -- For each n ∈ ℕ such that 100 ≤ n, there exists a pairwise unequal triplet {a, b, c} ⊆ [n, 2n]
  -- such that all pairwise sums are perfect squares. In practice, it will be easier to use
  -- a finite set B ⊆ [n, 2n] such that all pairwise unequal pairs of B sum to a perfect square
  -- noting that B has cardinality greater or equal to 3, by the explicit construction of the
  -- triplet {a, b, c} before.
  obtain ⟨B, hB, h₁, h₂⟩ := exists_finset_of_3_leq_card_with_pairs_summing_to_squares n hn,
  have hB : 2 * 1 < ((B ∩ (finset.Icc n (2 * n) \ A)) ∪ (B ∩ A)).card,
  { rw ← finset.inter_distrib_left,
    have hBinter : B ∩ ((finset.Icc n (2 * n) \ A) ∪ A) = B,
    { rw finset.inter_eq_left_iff_subset,
      simp only [finset.sdiff_union_self_eq_union],
      rw finset.union_eq_left_iff_subset.mpr hA,
      intros c hcB,
      simp only [finset.mem_Icc],
      exact h₂ c hcB },
    rw hBinter,
    exact nat.succ_le_iff.mp hB },
  -- Since B has cardinality greater or equal to 3, there must exist a subset C ⊆ B such that
  -- for any A ⊆ [n, 2n], either C ⊆ A or C ⊆ [n, 2n] \ A and C has cardinality greater
  -- or equal to 2.
  have hp₂ := finset.exists_subset_or_subset_of_two_mul_le_card hB,
  rcases hp₂ with (⟨C, hC, (hCA | hCA)⟩),
  -- First, we deal with the case when C ⊆ [n, 2n] \ A.
  { right,
    replace hC := nat.succ_le_iff.mp hC,
    rw finset.one_lt_card at hC,
    rcases hC with ⟨a, ha, b, hb, hab⟩,
    refine ⟨a, b, _, _, hab, h₁ a b _ _ hab⟩,
    { exact finset.mem_of_mem_inter_right (hCA ha) },
    { exact finset.mem_of_mem_inter_right (hCA hb) },
    { exact finset.mem_of_mem_inter_left (hCA ha) },
    { exact finset.mem_of_mem_inter_left (hCA hb) }},
  -- Then, we finish the proof in the case when C ⊆ A.
  { left,
    replace hC := nat.succ_le_iff.mp hC,
    rw finset.one_lt_card at hC,
    rcases hC with ⟨a, ha, b, hb, hab⟩,
    refine ⟨a, b, _, _, hab, h₁ a b _ _ hab⟩,
    { exact finset.mem_of_mem_inter_right (hCA ha) },
    { exact finset.mem_of_mem_inter_right (hCA hb) },
    { exact finset.mem_of_mem_inter_left (hCA ha) },
    { exact finset.mem_of_mem_inter_left (hCA hb) }},
end
