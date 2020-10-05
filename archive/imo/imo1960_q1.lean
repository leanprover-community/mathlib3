/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/

import data.nat.digits

open nat

/-!
# IMO 1960 Q1

Determine all three-digit numbers $N$ having the property that $N$ is divisible by 11, and
$\dfrac{N}{11}$ is equal to the sum of the squares of the digits of $N$.

Since Lean doesn't have a way to directly express problem statements of the form
"Determine all X satisfying Y", we express two predicates where proving that one implies the
other is equivalent to solving the problem. A human solver also has to discover the
second predicate.

In theory, we should be able to brute force this and check every number up to 1000.
In practice, the Lean tactics that are capable of checking a single number, like `norm_num`,
are not efficient enough to run a thousand times while compiling one file.
-/

def sum_of_squares (L : list ℕ) : ℕ := (list.map (λ x, x * x) L).sum

def problem_predicate (n : ℕ) :=
(nat.digits 10 n).length = 3 ∧ 11 ∣ n ∧ n / 11 = sum_of_squares (nat.digits 10 n)

def solution_predicate (n : ℕ) := n = 550 ∨ n = 803

/-
Proving that three digit numbers are the ones in [100, 1000).
-/

lemma not_zero (n : ℕ) (h1 : problem_predicate n) : n ≠ 0 :=
have h2: nat.digits 10 n ≠ list.nil, from list.ne_nil_of_length_eq_succ h1.left,
digits_ne_nil_iff_ne_zero.mp h2

lemma ge_100 (n : ℕ) (h1 : problem_predicate n) : n ≥ 100 :=
have h2 : 10^3 ≤ 10 * n, from begin
  rw ← h1.left,
  refine nat.base_pow_length_digits_le 10 n _ (not_zero n h1),
  simp,
end,
by linarith

lemma lt_1000 (n : ℕ) (h1: problem_predicate n) : n < 1000 :=
have h2 : n < 10^3, from begin
  rw ← h1.left,
  refine nat.lt_base_pow_length_digits _,
  simp,
end,
by linarith

/-
How to calculate the sum of square digits, so that we can quickly simplify a
sum_of_digit_squares expression.
These are basically "hints" to speed up norm_num.
-/

def sum_of_digit_squares (n : ℕ) := sum_of_squares (nat.digits 10 n)

lemma sods_zero : sum_of_digit_squares 0 = 0 :=
by norm_num [sum_of_digit_squares, sum_of_squares]

lemma digit_recursion (n : ℕ) (h1 : 0 < n) :
(nat.digits 10 n) = (n % 10) :: (nat.digits 10 (n / 10)) :=
begin
  have h2: n ≥ 1, by linarith,
  have h3: (n - 1) + 1 = n, from nat.sub_add_cancel h2,
  rw ← h3,
  refl,
end

lemma calc_sods (n : ℕ) (h : 0 < n) :
sum_of_digit_squares n = (n % 10) ^ 2 + (sum_of_digit_squares (n / 10)) :=
begin
  unfold sum_of_digit_squares,
  rw digit_recursion _ h,
  unfold sum_of_squares,
  simp [pow_two],
end

/-
This part is doing an exhaustive search.
-/

def fails_sum (c : ℕ) := c ≠ sum_of_digit_squares (c*11)

def multiples_of_11 (n : ℕ) (h1: problem_predicate n) :
∃ c : ℕ, ¬ fails_sum c ∧ 9 < c ∧ c < 91 ∧ n = c * 11 :=
begin
  have h2: ∃ c : ℕ, n = c * 11, from exists_eq_mul_left_of_dvd h1.right.left,
  cases h2 with c h3,
  use c,
  split,
  { have h4: c = (c * 11) / 11, by simp,
    have h5: c = n / 11, from h3.symm ▸ h4,
    unfold fails_sum,
    rw [h3.symm, h5],
    simp,
    exact h1.right.right },
  split,
  { have h6: n ≥ 100, from ge_100 n h1,
    linarith },
  have h7: n < 1000, from lt_1000 n h1,
  split,
  linarith,
  exact h3,
end

lemma step_helper (b c : ℕ) (h1 : b < c) : b + 1 = c ∨ b + 1 < c :=
begin
  have h2 : b + 1 ≤ c, from succ_le_iff.mpr h1,
  exact eq_or_lt_of_le h2
end

lemma iterative_step (c bound : ℕ) (h1 : fails_sum (bound + 1)) (h2 : fails_sum c ∨ bound < c) :
fails_sum c ∨ bound + 1 < c :=
begin
  cases h2,
  { left,
    exact h2 },
  have h3 : bound + 1 = c ∨ bound + 1 < c, from step_helper bound c h2,
  cases h3,
  { left,
    exact h3 ▸ h1 },
  right,
  exact h3,
end

lemma low_search (c : ℕ) (lower_bound: 9 < c) : fails_sum c ∨ 49 < c :=
begin
  iterate 40 {
    refine iterative_step _ _ _ _,
    norm_num [fails_sum, calc_sods, sods_zero],
  },
  right,
  exact lower_bound,
end

lemma mid_search (c : ℕ) (lower_bound : 50 < c) : fails_sum c ∨ 72 < c :=
begin
  iterate 22 {
    refine iterative_step _ _ _ _,
    norm_num [fails_sum, calc_sods, sods_zero],
  },
  right,
  exact lower_bound,
end

lemma high_search (c : ℕ) (lower_bound : 73 < c) : fails_sum c ∨ 90 < c :=
begin
  iterate 17 {
    refine iterative_step _ _ _ _,
    norm_num [fails_sum, calc_sods, sods_zero],
  },
  right,
  exact lower_bound,
end

/-
Now we just need to combine the results from the `search` lemmas.
-/

lemma right_direction (n : ℕ) : problem_predicate n → solution_predicate n :=
begin
  intro ppn,
  have h1 : ∃ c : ℕ, ¬ fails_sum c ∧ 9 < c ∧ c < 91 ∧ n = c * 11, from multiples_of_11 n ppn,
  cases h1 with c h2,
  have h3 : fails_sum c ∨ 49 < c, from low_search c h2.right.left,
  cases h3,
  exact absurd h3 h2.left,
  have h4 : 50 = c ∨ 50 < c, from step_helper 49 c h3,
  unfold solution_predicate,
  have h5 : n = c * 11, from h2.right.right.right,
  cases h4,
  { left,
    linarith },
  have h6 : fails_sum c ∨ 72 < c, from mid_search c h4,
  cases h6,
  exact absurd h6 h2.left,
  have h7 : 73 = c ∨ 73 < c, from step_helper 72 c h6,
  cases h7,
  { right,
    linarith },
  have h8 : fails_sum c ∨ 90 < c, from high_search c h7,
  cases h8,
  exact absurd h8 h2.left,
  linarith,
end

lemma left_direction (n : ℕ) : solution_predicate n → problem_predicate n :=
begin
  unfold solution_predicate,
  intro spn,
  cases spn,
  { rw spn,
    norm_num [problem_predicate, sum_of_squares] },
  rw spn,
  norm_num [problem_predicate, sum_of_squares],
end

theorem imo1960_q1 (n : ℕ) : problem_predicate n ↔ solution_predicate n :=
begin
  split,
  exact right_direction n,
  exact left_direction n,
end

