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
Let n≥100 be an integer. Ivan writes the numbers n, n+1,..., 2n each on different cards.
He then shuffles these n+1 cards, and divides them into two piles. Prove that at least one
of the piles contains two cards such that the sum of their numbers is a perfect square.
# Solution
We show there exists a triplet a, b, c ∈ [n , 2n] with a < b < c and each of the sums (a + b),
(b + c), (a + c) being a perfect square. Specifically, we consider the linear system of equations

  a + b = (2 * l - 1) ^ 2
  a + c = (2 * l) ^ 2
  b + c = (2 * l + 1) ^ 2

which can be solved to give

  a = 2 * l * l - 4 * l
  b = 2 * l * l + 1
  c = 2 * l * l + 4 * l

Therefore, it is enough to show that there exists a natural number l such that
n ≤ 2 * l * l - 4 * l and 2 * l * l + 4 * l ≤ 2 * n for n ≥ 100.

Then, by Pigeonhole principle, at least two numbers in the triplet must lie in the same pile, which
finishes the proof.
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

/- We will later make use of the fact that there exists (l : ℕ) such that
n ≤ 2 * l * l - 4 * l and 2 * l * l + 4 * l ≤ 2 * n for n ≥ 107. -/
lemma exists_numbers_in_interval (n : ℕ) (hn : 107 ≤ n): ∃ (l : ℕ),
  (n + 4 * l ≤ 2 * l * l ∧ 2 * l * l + 4 * l ≤ 2 * n) :=
begin
  suffices : ∃ (l : ℕ), 2 + sqrt (4 + 2 * n) ≤ 2 * (l : ℝ) ∧ (l : ℝ) ≤ sqrt (1 + n) - 1,
  { cases this with l t,
    use l,
    refine ⟨lower_bound n l t.1, upper_bound n l t.2⟩ },
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
  { rw [floor_nonneg, le_sub, sub_zero, le_sqrt],
    all_goals { norm_cast, linarith } },
end

lemma exists_triplet_summing_to_squares (n : ℕ) (hn : 100 ≤ n):
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
      ⟨_,⟨_,⟨_,⟨_,⟨2 * l - 1, _⟩,⟨2 * l, _⟩,2 * l + 1, _⟩⟩⟩⟩⟩,
      all_goals { zify [h₁, h₂], linarith } },
    { exfalso,
      simp only [not_lt] at p,
      interval_cases l; linarith }},
  -- Otherwise, if 100 ≤ n < 107, then it suffices to consider explicit
  -- construction of a triplet {a, b, c}, which is constructed by setting l=9
  -- in the argument at the start of the file.
  { refine ⟨126, 163, 198, _, _, _, _,⟨17, _⟩, ⟨18, _⟩, 19, _⟩; linarith },
end

-- We will need a lemma, stating that if a given number a ∈ [n, 2n]
-- does not belong to A ⊆ [n, 2n], then it belongs to [n, 2n] \ A.
lemma finset.Ico.mem_compl_iff_nmem_subset {a n : ℕ} (A : finset ℕ)
  (h : a ∈ finset.Ico n (2 * n + 1)) : a ∉ A ↔ a ∈ finset.Ico n (2 * n + 1) \ A :=
begin
  rw finset.mem_sdiff,
  split,
  { intro ha,
    exact ⟨h, ha⟩ },
  { intro ha,
    exact ha.2 },
end

theorem IMO_2021_Q1 : ∀ (n : ℕ), 100 ≤ n → ∀ (A ⊆ finset.Ico n (2 * n + 1)),
  (∃ (a b ∈ A), a ≠ b ∧ ∃ (k : ℕ), a + b = k * k) ∨
  (∃ (a b ∈ finset.Ico n (2 * n + 1) \ A), a ≠ b ∧ ∃ (k : ℕ), a + b = k * k) :=
begin
  intros n hn A hA,
  -- There exists a pairwise unequal triplet a, b, c ∈ ℕ
  -- such that all pairwise sums are perfect squares.
  have p := exists_triplet_summing_to_squares n hn,
  rcases p with ⟨a, b, c, hna, hab, hbc, hcn, p⟩,
  -- Now, we will show that indeed a, b, c ∈ [n, 2n]
  have ha : a ∈ finset.Ico n (2 * n + 1),
  { rw finset.Ico.mem,
    split;
    linarith },
  have hb : b ∈ finset.Ico n (2 * n + 1),
  { rw finset.Ico.mem,
    split;
    linarith },
  have hc : c ∈ finset.Ico n (2 * n + 1),
  { rw finset.Ico.mem,
    split;
    linarith },
  -- Consider by cases based on whether each of {a, b, c} belongs to the 'first pile' A or not.
  -- In each case, we can find two members of the triplet in the same pile, as required.
  by_cases h₁: a ∈ A,
  { by_cases h₂: b ∈ A,
    { left,
      refine ⟨a, b, h₁, h₂, _, p.1⟩,
      exact ne_of_lt hab },
    { by_cases h₃ : c ∈ A,
      { left,
        refine ⟨c, a, h₃, h₁, _, p.2.1⟩,
        linarith },
      { rw finset.Ico.mem_compl_iff_nmem_subset A hb at h₂,
        rw finset.Ico.mem_compl_iff_nmem_subset A hc at h₃,
        right,
        refine ⟨b, c, h₂, h₃, _, p.2.2⟩,
        exact ne_of_lt hbc }}},
  { rw finset.Ico.mem_compl_iff_nmem_subset A ha at h₁,
    by_cases h₂ : b ∈ A,
    { by_cases h₃ : c ∈ A,
      { left,
        refine ⟨b, c, h₂, h₃, _, p.2.2⟩,
        linarith },
      { rw finset.Ico.mem_compl_iff_nmem_subset A hc at h₃,
        right,
        refine ⟨c, a, h₃, h₁, _, p.2.1⟩,
        linarith }},
      { rw finset.Ico.mem_compl_iff_nmem_subset A hb at h₂,
        right,
        refine ⟨a, b, h₁, h₂, _, p.1⟩,
        linarith }},
end
