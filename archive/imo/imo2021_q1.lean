import tactic data.real.sqrt

noncomputable theory

open real

/-
# IMO 2021 Q1
Let n≥100 be an integer. Ivan writes the numbers n, n+1,..., 2n each on different cards.
He then shuffles these n+1 cards, and divides them into two piles. Prove that at least one
of the piles contains two cards such that the sum of their numbers is a perfect square.
# Solution
We prove the required claim by constructing a triplet of pairwise unequal
natural numbers a, b, c ∈ [n, 2n], with each sum of each pair being a perfect square. Then, by
Pigeonhole principle, at least two numbers in the triplet must lie in the same pile, which
finishes the proof.
-/
lemma lower_bound (n : ℕ) (l : ℤ) (hl : 2 * (l : ℝ) ≥ 2 + sqrt (4 + 2 * n)) :
  (n : ℤ) + 4 * l ≤ 2 * l * l :=
begin
  have h₁ : sqrt (4 + 2 * n) ≤ 2 * l - 2 := by linarith,
  replace h₁ := (sqrt_le_iff.1 h₁).2,
  norm_cast at h₁, push_cast at h₁,
  linarith,
end

lemma upper_bound (n : ℕ) (l : ℤ) (hl₁ : l ≥ 0) (hl₂ : (l : ℝ) ≤ sqrt (1 + n) - 1):
2 * l * l + 4 * l ≤ 2 * n :=
begin
  have h₁ : (l : ℝ) + 1 ≤ sqrt (1 + n) := by linarith,
  rw le_sqrt at h₁,
  ring_exp at h₁,
  norm_cast at h₁, push_cast at h₁,
  linarith,
  repeat {norm_cast, linarith},
end


lemma radical_inequality {n : ℕ} (h : n ≥ 107) : sqrt (4 + 2 * n) ≤ 2 * (sqrt (1 + n) - 3) :=
begin
  rw sqrt_le_iff,
  split,
  { norm_num,
    rw le_sqrt,
    repeat {norm_cast, linarith}},
  ring_exp,
  rw [pow_two, ← sqrt_mul, sqrt_mul_self],
  suffices : 24 * sqrt (1 + n) ≤ 2 * n + 36,
  linarith,
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
  repeat {norm_cast, linarith},
  repeat {norm_num, apply sqrt_nonneg},
end

/-We will later make use of the fact that there exists (l : ℕ) such that
n ≤ 2 * l * l - 4 * l and 2 * l * l + 4 * l ≤ 2 * n for n ≥ 107.
-/
lemma exists_numbers_in_interval (n : ℕ) (hn : n ≥ 107): ∃ (l : ℤ), l ≥ 0 ∧
((n : ℤ) + 4 * l ≤ 2 * l * l ∧ 2 * l * l + 4 * l ≤ 2 * n) :=
begin
  suffices : ∃ (l : ℤ), l ≥ 0 ∧ 2 * (l : ℝ) ≥ 2 + sqrt (4 + 2 * n) ∧ (l : ℝ) ≤ sqrt (1 + n) - 1,
  cases this with l t,
  use l,
  refine ⟨t.1, ⟨lower_bound n l t.2.1, upper_bound n l t.1 t.2.2⟩⟩,
  use floor (sqrt (1 + n) - 1),
  split,
  { simp only [ge_iff_le],
    rw floor_nonneg,
    norm_num,
    rw le_sqrt,
    repeat {norm_cast, linarith}},
  refine ⟨_, floor_le (sqrt (1 + n) - 1)⟩,
  { suffices : 2 * (sqrt (1 + n) - 2) ≥ 2 + sqrt (4 + 2 * n),
    apply le_trans this _,
    simp only [mul_le_mul_left, zero_lt_bit0, zero_lt_one],
    suffices : sqrt (1 + n) - 1 ≤ ↑⌊sqrt (1 + n) - 1⌋ + 1,
    linarith,
    have t :  (⌈sqrt (1 + n) - 1⌉:ℝ) ≤ ⌊sqrt (1 + n) - 1⌋ + 1,
    norm_cast,
    exact ceil_le_floor_add_one _,
    apply le_trans _ t,
    exact le_ceil (sqrt (1 + ↑n) - 1),
    suffices : sqrt (4 + 2 * n) ≤ 2 * (sqrt (1 + n) - 3),
    linarith,
    exact radical_inequality hn },
end

/-
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
-/

lemma exists_triplet_summing_to_squares (n : ℕ) (hn : n ≥ 100): (∃ (a b c : ℤ),
(n : ℤ) ≤ a ∧ a < b ∧ b < c ∧ c ≤ 2 * n ∧  (∃ (k : ℤ), a + b = k * k) ∧
(∃ (l : ℤ), a + c = l * l) ∧ (∃ (m : ℤ), b + c = m * m)) :=
begin
  --If n ≥ 107, we do not explicitly construct the triplet but use an existence
  --argument from lemma above.
  by_cases p : n ≥ 107,
  have h := exists_numbers_in_interval n p,
  cases h with l hl,
  use (2 * l * l - 4 * l),
  use (2 * l * l + 1),
  use (2 * l * l + 4 * l),
  refine ⟨_,⟨_,⟨_,⟨_,⟨_, ⟨_, _⟩⟩⟩⟩⟩⟩,
  { rw le_sub_iff_add_le,
    exact hl.2.1 },
  { nlinarith },
  { nlinarith },
  { exact hl.2.2},
  { use (2 * l - 1),
    ring_exp_eq },
  { use (2 * l),
    ring_exp_eq },
  { use(2 * l + 1),
    ring_exp_eq },
    --Otherwise, if 100 ≤ n < 107, then it suffices to consider explicit
    --construction of a triplet {a, b, c}, which is constructed by setting l=9
    --in the argument above this lemma.
  { use 126,
    use 163,
    use 198,
    repeat {split, linarith},
    refine ⟨_,⟨_,_⟩⟩,
    use 17,
    linarith,
    use 18,
    linarith,
    use 19,
    linarith },
end

lemma mem_compl_iff_nmem_subset {A : finset ℕ} {a b c n : ℕ}
(t : A ⊆ finset.range(2 * n + 1)\finset.range n) (h₁ : (n : ℤ) ≤ a)
(h₂ : (a : ℤ) < b) (h₃ : (b : ℤ) < c) (h₄ : (c : ℤ) ≤ 2 * n) :
(a ∉ A ↔ a ∈ (finset.range (2 * n + 1)\finset.range n)\A)
∧ (b ∉ A ↔ b ∈ (finset.range (2 * n + 1)\finset.range n)\A) ∧
(c ∉ A ↔ c ∈ (finset.range (2 * n + 1)\finset.range n)\A) :=
begin
  norm_cast at h₁,
  norm_cast at h₂,
  norm_cast at h₃,
  norm_cast at h₄,
  refine ⟨⟨_,_⟩, ⟨⟨_,_⟩,⟨_,_⟩⟩⟩,
  { intro ha,
    simp only [finset.mem_sdiff, finset.mem_range],
    refine ⟨⟨_,_⟩,ha⟩,
    repeat {linarith}},
  { intro ha,
    simp only [finset.mem_sdiff, finset.mem_range] at ha,
    exact ha.2 },
  { intro hb,
    simp only [finset.mem_sdiff, finset.mem_range],
    refine ⟨⟨_,_⟩,hb⟩,
    repeat {linarith}},
  { intro hb,
    simp only [finset.mem_sdiff, finset.mem_range] at hb,
    exact hb.2 },
   {intro hc,
    simp only [finset.mem_sdiff, finset.mem_range],
    refine ⟨⟨_,_⟩,hc⟩,
    repeat {linarith}},
  { intro hc,
    simp only [finset.mem_sdiff, finset.mem_range] at hc,
    exact hc.2 },
end


theorem IMO_2021_Q1 : ∀ (n : ℕ), n ≥ 100 → ∀ (A ⊆ finset.range(2 * n + 1)\finset.range n),
(∃ (a b : A), a ≠ b ∧ ∃ (k : ℤ), (a : ℤ) + b = k * k) ∨
(∃ (a b: (finset.range (2 * n + 1)\finset.range n)\A), a ≠ b ∧ ∃(k : ℤ), (a : ℤ) + b=k * k) :=
begin
  intros n hn A hA,
  -- There exists a pairwise unequal triplet a, b, c ∈ [n, 2n]
  --such that all pairwise sums are perfect squares.
  have p := exists_triplet_summing_to_squares n hn,
  rcases p with ⟨a, b, c, ⟨han, hba, hcb, hnc, p⟩⟩,
  lift a to ℕ,
  lift b to ℕ,
  lift c to ℕ,
  -- Consider by cases based on whether each of {a, b, c} belongs to the 'first pile' A or not.
  -- In each case, we can find two members of the triplet in the same pile, as required.
  by_cases h₁: a ∈ A,
  by_cases h₂: b ∈ A,
  left,
  use a,
  exact h₁,
  use b,
  exact h₂,
  refine ⟨_, p.1⟩,
  { simp only [subtype.mk_eq_mk, ne.def],
    linarith },
  by_cases h₃ : c ∈ A,
  left,
  use a,
  exact h₁,
  use c,
  exact h₃,
  refine ⟨_,p.2.1⟩,
  { simp only [subtype.mk_eq_mk, ne.def],
    linarith },
  rw (mem_compl_iff_nmem_subset hA han hba hcb hnc).2.1 at h₂,
  rw (mem_compl_iff_nmem_subset hA han hba hcb hnc).2.2 at h₃,
  right,
  use b,
  exact h₂,
  use c,
  exact h₃,
  refine ⟨_, p.2.2⟩,
  { simp only [subtype.mk_eq_mk, ne.def],
    linarith },
  rw (mem_compl_iff_nmem_subset hA han hba hcb hnc).1 at h₁,
  by_cases h₂ : b ∈ A,
  by_cases h₃ : c ∈ A,
  left,
  use b,
  exact h₂,
  use c,
  exact h₃,
  refine ⟨_, p.2.2⟩,
  { simp only [subtype.mk_eq_mk, ne.def],
    linarith },
  rw (mem_compl_iff_nmem_subset hA han hba hcb hnc).2.2 at h₃,
  right,
  use a,
  exact h₁,
  use c,
  exact h₃,
  refine ⟨_, p.2.1⟩,
  { simp only [subtype.mk_eq_mk, ne.def],
    linarith },
  rw (mem_compl_iff_nmem_subset hA han hba hcb hnc).2.1 at h₂,
  right,
  use a,
  exact h₁,
  use b,
  exact h₂,
  refine ⟨_, p.1⟩,
  { simp only [subtype.mk_eq_mk, ne.def],
    linarith },
  repeat {linarith},
end
