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

lemma lower_bound (n l : ℕ) (hl : 2 + sqrt (4 + 2 * n) ≤ 2 * (l : ℝ)) :
  (n : ℕ) + 4 * l ≤ 2 * l * l :=
begin
  have h₁ : sqrt (4 + 2 * n) ≤ 2 * l - 2 := by linarith,
  replace h₁ := (sqrt_le_iff.1 h₁).2,
  ring_exp at h₁,
  norm_num at h₁,
  norm_cast at h₁,
  linarith,
end

lemma upper_bound (n l : ℕ) (hl₂ : (l : ℝ) ≤ sqrt (1 + n) - 1) :
  2 * l * l + 4 * l ≤ 2 * n :=
begin
  have h₁ : (l : ℝ) + 1 ≤ sqrt (1 + n) := by linarith,
  rw le_sqrt at h₁,
  ring_exp at h₁, norm_num at h₁,
  norm_cast at h₁,
  linarith,
  all_goals { norm_cast, linarith },
end


lemma radical_inequality {n : ℕ} (h : n ≥ 107) : sqrt (4 + 2 * n) ≤ 2 * (sqrt (1 + n) - 3) :=
begin
  rw sqrt_le_iff,
  split,
  { norm_num,
    rw le_sqrt,
    all_goals { norm_cast, linarith }},
  { ring_exp,
    rw [pow_two, ← sqrt_mul, sqrt_mul_self],
    suffices : 24 * sqrt (1 + n) ≤ 2 * n + 36,
    { linarith },
    rw mul_self_le_mul_self_iff,
    ring_exp,
    rw [pow_two, ← sqrt_mul, sqrt_mul_self],
    --Not splitting into cases lead to a deterministic timeout on my machine
    by_cases p: n ≥ 108,
    norm_cast,
    nlinarith,
    have : n = 107 := by linarith,
    subst this,
    norm_num,
    swap 3,
    { norm_num,
      apply sqrt_nonneg },
    all_goals { norm_cast, linarith }},
end

/- We will later make use of the fact that there exists (l : ℕ) such that
n ≤ 2 * l * l - 4 * l and 2 * l * l + 4 * l ≤ 2 * n for n ≥ 107. -/
lemma exists_numbers_in_interval (n : ℕ) (hn : n ≥ 107): ∃ (l : ℕ),
  (n + 4 * l ≤ 2 * l * l ∧ 2 * l * l + 4 * l ≤ 2 * n) :=
begin
  suffices : ∃ (l : ℕ), 2 * (l : ℝ) ≥ 2 + sqrt (4 + 2 * n) ∧ (l : ℝ) ≤ sqrt (1 + n) - 1,
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
  { suffices : 2 * (sqrt (1 + n) - 2) ≥ 2 + sqrt (4 + 2 * n),
    { apply le_trans this _,
      simp only [mul_le_mul_left, zero_lt_bit0, zero_lt_one],
      rw hx,
      suffices : sqrt (1 + n) - 1 ≤ ↑⌊sqrt (1 + n) - 1⌋ + 1,
      { linarith },
      have t :  (⌈sqrt (1 + n) - 1⌉:ℝ) ≤ ⌊sqrt (1 + n) - 1⌋ + 1,
        norm_cast,
        exact ceil_le_floor_add_one _,
      apply le_trans _ t,
      exact le_ceil (sqrt (1 + ↑n) - 1) },
      suffices : sqrt (4 + 2 * n) ≤ 2 * (sqrt (1 + n) - 3),
      { linarith },
    exact radical_inequality hn },
  { rw hx,
    exact floor_le _ },
  { rw [floor_nonneg, le_sub, sub_zero, le_sqrt],
    all_goals { norm_cast, linarith }},

end

lemma exists_triplet_summing_to_squares (n : ℕ) (hn : n ≥ 100): (∃ (a b c : ℕ),
  n ≤ a ∧ a < b ∧ b < c ∧ c ≤ 2 * n ∧  (∃ (k : ℕ), a + b = k * k) ∧
  (∃ (l : ℕ), c + a = l * l) ∧ (∃ (m : ℕ), b + c = m * m)) :=
begin
  --If n ≥ 107, we do not explicitly construct the triplet but use an existence
  --argument from lemma above.
  by_cases p : n ≥ 107,
  { have h := exists_numbers_in_interval n p,
    cases h with l hl,
    use (2 * l * l - 4 * l),
    use (2 * l * l + 1),
    use (2 * l * l + 4 * l),
    by_cases p : l > 1,
    refine ⟨_,⟨_,⟨_,⟨_,⟨_, ⟨_, _⟩⟩⟩⟩⟩⟩,
    { exact nat.le_sub_right_of_add_le hl.1 },
    { exact (2 * l * l).sub_lt_succ (4 * l) },
    { linarith },
    { exact hl.2 },
    { use (2 * l - 1),
      have h₁ : 1 ≤ 2 * l := by linarith,
      have h₂ : 4 * l ≤ 2 * l * l := by linarith,
      zify [h₁, h₂],
      ring_exp_eq },
    { use (2 * l),
      have h₁ : 4 * l ≤ 2 * l * l := by linarith,
      zify [h₁],
      ring_exp_eq },
    { use(2 * l + 1),
      ring_exp_eq,
    },
      --Otherwise, if 100 ≤ n < 107, then it suffices to consider explicit
      --construction of a triplet {a, b, c}, which is constructed by setting l=9
      --in the argument at the start of the file.
    { exfalso,
      simp only [not_lt] at p,
      interval_cases l,
      all_goals {linarith }}},
  { refine ⟨126, 163, 198, _, _, _, _, ⟨⟨17, _⟩,⟨⟨18, _⟩,⟨19, _⟩⟩⟩⟩,
    all_goals { linarith }},
end

lemma mem_compl_iff_nmem_subset {A : finset ℕ} {a b c n : ℕ}
(t : A ⊆ finset.Ico n (2 * n + 2)) (h₁ : n ≤ a)
(h₂ : a < b) (h₃ : b < c) (h₄ : c ≤ 2 * n) :
(a ∉ A ↔ a ∈ finset.Ico n (2 * n + 2) \ A) ∧
(b ∉ A ↔ b ∈ finset.Ico n (2 * n + 2) \ A) ∧
(c ∉ A ↔ c ∈ finset.Ico n (2 * n + 2) \ A) :=
begin
  refine ⟨⟨_,_⟩, ⟨⟨_,_⟩,⟨_,_⟩⟩⟩,
  { intro ha,
    simp only [finset.Ico.mem, finset.mem_sdiff],
    refine ⟨⟨_,_⟩,ha⟩,
    all_goals { linarith }},
  { intro ha,
    simp only [finset.mem_sdiff, finset.mem_range] at ha,
    exact ha.2 },
  { intro hb,
    simp only [finset.Ico.mem, finset.mem_sdiff],
    refine ⟨⟨_,_⟩,hb⟩,
    all_goals { linarith }},
  { intro hb,
    simp only [finset.mem_sdiff, finset.mem_range] at hb,
    exact hb.2 },
  { intro hc,
    simp only [finset.Ico.mem, finset.mem_sdiff],
    refine ⟨⟨_,_⟩,hc⟩,
    all_goals { linarith }},
  { intro hc,
    simp only [finset.mem_sdiff, finset.mem_range] at hc,
    exact hc.2 },
end


theorem IMO_2021_Q1 : ∀ (n : ℕ), n ≥ 100 → ∀ (A ⊆ finset.Ico n (2 * n + 2)),
  (∃ (a b : A), a ≠ b ∧ ∃ (k : ℕ), (a:ℕ) + b = k * k) ∨
  (∃ (a b : finset.Ico n (2 * n + 2) \ A), a ≠ b ∧ ∃(k : ℕ), (a:ℕ) + b = k * k) :=
begin
  intros n hn A hA,
  -- There exists a pairwise unequal triplet a, b, c ∈ [n, 2n]
  -- such that all pairwise sums are perfect squares.
  have p := exists_triplet_summing_to_squares n hn,
  rcases p with ⟨a, b, c, ⟨han, hba, hcb, hnc, p⟩⟩,
  -- Consider by cases based on whether each of {a, b, c} belongs to the 'first pile' A or not.
  -- In each case, we can find two members of the triplet in the same pile, as required.
  by_cases h₁: a ∈ A,
  { by_cases h₂: b ∈ A,
    { left,
      use a,
      exact h₁,
      use b,
      exact h₂,
      refine ⟨_, p.1⟩,
      { simp only [subtype.mk_eq_mk, ne.def],
        linarith}},
    { by_cases h₃ : c ∈ A,
      { left,
        use c,
        exact h₃,
        use a,
        exact h₁,
        refine ⟨_,p.2.1⟩,
        { simp only [subtype.mk_eq_mk, ne.def],
          linarith }},
      { rw (mem_compl_iff_nmem_subset hA han hba hcb hnc).2.1 at h₂,
        rw (mem_compl_iff_nmem_subset hA han hba hcb hnc).2.2 at h₃,
        right,
        use b,
        exact h₂,
        use c,
        exact h₃,
        refine ⟨_, p.2.2⟩,
        { simp only [subtype.mk_eq_mk, ne.def],
          linarith }}}},
  { rw (mem_compl_iff_nmem_subset hA han hba hcb hnc).1 at h₁,
    by_cases h₂ : b ∈ A,
    { by_cases h₃ : c ∈ A,
      { left,
        use b,
        exact h₂,
        use c,
        exact h₃,
        refine ⟨_, p.2.2⟩,
        { simp only [subtype.mk_eq_mk, ne.def],
          linarith }},
      { rw (mem_compl_iff_nmem_subset hA han hba hcb hnc).2.2 at h₃,
        right,
        use c,
        exact h₃,
        use a,
        exact h₁,
        refine ⟨_, p.2.1⟩,
        { simp only [subtype.mk_eq_mk, ne.def],
          linarith }}},
      { rw (mem_compl_iff_nmem_subset hA han hba hcb hnc).2.1 at h₂,
        right,
        use a,
        exact h₁,
        use b,
        exact h₂,
        refine ⟨_, p.1⟩,
        { simp only [subtype.mk_eq_mk, ne.def],
          linarith }}},
end
