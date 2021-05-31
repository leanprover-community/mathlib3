/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/

import data.nat.digits

/-!
# IMO 1962 Q1

Find the smallest natural number $n$ which has the following properties:

(a) Its decimal representation has 6 as the last digit.

(b) If the last digit 6 is erased and placed in front of the remaining digits,
the resulting number is four times as large as the original number $n$.

Since Lean does not explicitly express problems of the form "find the smallest number satisfying X",
we define the problem as a predicate, and then prove a particular number is the smallest member
of a set satisfying it.
-/

open nat

def problem_predicate (n : ℕ) : Prop :=
(digits 10 n).head = 6 ∧ of_digits 10 ((digits 10 n).tail.concat 6) = 4 * n

/-!
First, it's inconvenient to work with digits, so let's simplify them out of the problem.
-/

abbreviation problem_predicate' (c n : ℕ) : Prop :=
n = 10 * c + 6 ∧ 6 * 10 ^ (digits 10 c).length + c = 4 * n

lemma without_digits {n : ℕ} (h1 : problem_predicate n) :
∃ c : ℕ, problem_predicate' c n :=
begin
  use n / 10,
  cases n,
  { have h2 : ¬ problem_predicate 0, by norm_num [problem_predicate],
    contradiction },
  { rw [problem_predicate, digits_def' (dec_trivial : 2 ≤ 10) n.succ_pos,
        list.head, list.tail_cons, list.concat_eq_append] at h1,
    split,
    { rw [← h1.left, div_add_mod (n+1) 10], },
    { rw [← h1.right, of_digits_append, of_digits_digits,
          of_digits_singleton, add_comm, mul_comm], }, },
end

/-!
Now we can eliminate possibilities for `(digits 10 c).length` until we get to the one that works.
-/

lemma case_0_digit {c n : ℕ} (h1 : (digits 10 c).length = 0) : ¬ problem_predicate' c n :=
begin
  intro h2,
  have h3 : 6 * 10 ^ 0 + c = 6 * 10 ^ (digits 10 c).length + c, by rw h1,
  have h4 : 6 * 10 ^ 0 + c = 4 * (10 * c + 6), by rw [h3, h2.right, h2.left],
  linarith,
end

lemma case_1_digit {c n : ℕ} (h1 : (digits 10 c).length = 1) : ¬ problem_predicate' c n :=
begin
  intro h2,
  have h3 : 6 * 10 ^ 1 + c = 6 * 10 ^ (digits 10 c).length + c, by rw h1,
  have h4 : 6 * 10 ^ 1 + c = 4 * (10 * c + 6), by rw [h3, h2.right, h2.left],
  have h6 : c > 0, by linarith,
  linarith,
end

lemma case_2_digit {c n : ℕ} (h1 : (digits 10 c).length = 2) : ¬ problem_predicate' c n :=
begin
  intro h2,
  have h3 : 6 * 10 ^ 2 + c = 6 * 10 ^ (digits 10 c).length + c, by rw h1,
  have h4 : 6 * 10 ^ 2 + c = 4 * (10 * c + 6), by rw [h3, h2.right, h2.left],
  have h5 : c > 14, by linarith,
  linarith
end

lemma case_3_digit {c n : ℕ} (h1 : (digits 10 c).length = 3) : ¬ problem_predicate' c n :=
begin
  intro h2,
  have h3 : 6 * 10 ^ 3 + c = 6 * 10 ^ (digits 10 c).length + c, by rw h1,
  have h4 : 6 * 10 ^ 3 + c = 4 * (10 * c + 6), by rw [h3, h2.right, h2.left],
  have h5 : c > 153, by linarith,
  linarith
end

lemma case_4_digit {c n : ℕ} (h1 : (digits 10 c).length = 4) : ¬ problem_predicate' c n :=
begin
  intro h2,
  have h3 : 6 * 10 ^ 4 + c = 6 * 10 ^ (digits 10 c).length + c, by rw h1,
  have h4 : 6 * 10 ^ 4 + c = 4 * (10 * c + 6), by rw [h3, h2.right, h2.left],
  have h5 : c > 1537, by linarith,
  linarith
end

/-- Putting this inline causes a deep recursion error, so we separate it out. -/
lemma helper_5_digit {c : ℤ} (h : 6 * 10 ^ 5 + c = 4 * (10 * c + 6)) : c = 15384 := by linarith

lemma case_5_digit {c n : ℕ} (h1 : (digits 10 c).length = 5) (h2 : problem_predicate' c n) :
  c = 15384 :=
begin
  have h3 : 6 * 10 ^ 5 + c = 6 * 10 ^ (digits 10 c).length + c, by rw h1,
  have h4 : 6 * 10 ^ 5 + c = 4 * (10 * c + 6), by rw [h3, h2.right, h2.left],
  zify at *,
  exact helper_5_digit h4
end

/--
`linarith` fails on numbers this large, so this lemma spells out some of the arithmetic
that normally would be automated.
-/
lemma case_more_digits {c n : ℕ} (h1 : (digits 10 c).length ≥ 6) (h2 : problem_predicate' c n) :
  n ≥ 153846 :=
begin
  have h3 : c ≠ 0,
  { intro h4,
    have h5 : (digits 10 c).length = 0, by simp [h4],
    exact case_0_digit h5 h2 },
  have h6 : 2 ≤ 10, from dec_trivial,
  calc
    n ≥ 10 * c                    : le.intro h2.left.symm
  ... ≥ 10 ^ (digits 10 c).length : base_pow_length_digits_le 10 c h6 h3
  ... ≥ 10 ^ 6                    : (pow_le_iff_le_right h6).mpr h1
  ... ≥ 153846                    : by norm_num,
end

/-!
Now we combine these cases to show that 153846 is the smallest solution.
-/

lemma satisfied_by_153846 : problem_predicate 153846 :=
by norm_num [problem_predicate, digits_def', of_digits]

lemma no_smaller_solutions (n : ℕ) (h1 : problem_predicate n) : n ≥ 153846 :=
begin
  cases without_digits h1 with c h2,
  have h3 : (digits 10 c).length < 6 ∨ (digits 10 c).length ≥ 6, by apply lt_or_ge,
  cases h3,
  case or.inr
  { exact case_more_digits h3 h2, },
  case or.inl
  { interval_cases (digits 10 c).length with h,
    { exfalso, exact case_0_digit h h2 },
    { exfalso, exact case_1_digit h h2 },
    { exfalso, exact case_2_digit h h2 },
    { exfalso, exact case_3_digit h h2 },
    { exfalso, exact case_4_digit h h2 },
    { have h4 : c = 15384, from case_5_digit h h2,
      have h5 : n = 10 * 15384 + 6, from h4 ▸ h2.left,
      norm_num at h5,
      exact h5.ge, }, },
end

theorem imo1962_q1 : is_least {n | problem_predicate n} 153846 :=
⟨satisfied_by_153846, no_smaller_solutions⟩
