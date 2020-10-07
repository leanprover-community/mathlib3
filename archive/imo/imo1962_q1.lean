/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/

import data.nat.digits

open nat

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

def problem_predicate (n : ℕ) :=
(nat.digits 10 n).head = 6 ∧ of_digits 10 ((nat.digits 10 n).tail.concat 6) = 4 * n

/-
First, it's inconvenient to work with digits, so let's simplify them out of the problem.
-/

lemma digit_recursion (n : ℕ) (h1 : n > 0) :
  (nat.digits 10 n) = (n % 10) :: (nat.digits 10 (n / 10)) :=
by rw [nat.digits, nat.digits_aux_def _ _ _ h1]

lemma without_digits (n : ℕ) (h1 : problem_predicate n) :
∃ c : ℕ, n = 10 * c + 6 ∧ 6 * 10 ^ (nat.digits 10 c).length + c = 4 * n :=
begin
  use n / 10,
  have h2 : ¬ problem_predicate 0, by norm_num [problem_predicate],
  have h3 : n = 0 ∨ n ≠ 0, from em(n = 0),
  cases h3,
  { have h4 : problem_predicate 0, from h3 ▸ h1,
    finish },
  unfold problem_predicate at h1,
  rw digit_recursion at h1,
  simp at h1,
  split,
  { have h5 : (n % 10) + 10 * (n / 10) = n, from mod_add_div n 10,
    linarith },
  { rw ← h1.right,
    simp [of_digits_append, of_digits_digits],
    ring },
  exact nat.pos_of_ne_zero h3
end

/-
Now we can solve for each possibility of (nat.digits 10 c).length until we get to the one that works.
-/

lemma case_0_digit (c n : ℕ) (h1 : (nat.digits 10 c).length = 0)
(h2 : n = 10 * c + 6 ∧ 6 * 10 ^ (nat.digits 10 c).length + c = 4 * n) : false :=
begin
  have h3 : 6 * 10 ^ 0 + c = 6 * 10 ^ (nat.digits 10 c).length + c, by rw h1,
  have h4 : 6 * 10 ^ 0 + c = 4 * (10 * c + 6), by rw [h3, h2.right, h2.left],
  linarith,
end

lemma case_1_digit (c n : ℕ) (h1 : (nat.digits 10 c).length = 1)
(h2 : n = 10 * c + 6 ∧ 6 * 10 ^ (nat.digits 10 c).length + c = 4 * n) : false :=
begin
  have h3 : 6 * 10 ^ 1 + c = 6 * 10 ^ (nat.digits 10 c).length + c, by rw h1,
  have h4 : 6 * 10 ^ 1 + c = 4 * (10 * c + 6), by rw [h3, h2.right, h2.left],
  have h6 : c > 0, by linarith,
  linarith,
end

lemma case_2_digit (c n : ℕ) (h1 : (nat.digits 10 c).length = 2)
(h2 : n = 10 * c + 6 ∧ 6 * 10 ^ (nat.digits 10 c).length + c = 4 * n) : false :=
begin
  have h3 : 6 * 10 ^ 2 + c = 6 * 10 ^ (nat.digits 10 c).length + c, by rw h1,
  have h4 : 6 * 10 ^ 2 + c = 4 * (10 * c + 6), by rw [h3, h2.right, h2.left],
  have h5 : c > 14, by linarith,
  linarith
end

lemma case_3_digit (c n : ℕ) (h1 : (nat.digits 10 c).length = 3)
(h2 : n = 10 * c + 6 ∧ 6 * 10 ^ (nat.digits 10 c).length + c = 4 * n) : false :=
begin
  have h3 : 6 * 10 ^ 3 + c = 6 * 10 ^ (nat.digits 10 c).length + c, by rw h1,
  have h4 : 6 * 10 ^ 3 + c = 4 * (10 * c + 6), by rw [h3, h2.right, h2.left],
  have h5 : c > 153, by linarith,
  linarith
end

lemma case_4_digit (c n : ℕ) (h1 : (nat.digits 10 c).length = 4)
(h2 : n = 10 * c + 6 ∧ 6 * 10 ^ (nat.digits 10 c).length + c = 4 * n) : false :=
begin
  have h3 : 6 * 10 ^ 4 + c = 6 * 10 ^ (nat.digits 10 c).length + c, by rw h1,
  have h4 : 6 * 10 ^ 4 + c = 4 * (10 * c + 6), by rw [h3, h2.right, h2.left],
  have h5 : c > 1537, by linarith,
  linarith
end

/- Putting this inline causes a deep recursion error, so we separate it out. -/
lemma helper_5_digit (c : ℤ) (h : 6 * 10 ^ 5 + c = 4 * (10 * c + 6)) : c = 15384 := by linarith

lemma case_5_digit (c n : ℕ) (h1 : (nat.digits 10 c).length = 5)
(h2 : n = 10 * c + 6 ∧ 6 * 10 ^ (nat.digits 10 c).length + c = 4 * n) : c = 15384 :=
begin
  have h3 : 6 * 10 ^ 5 + c = 6 * 10 ^ (nat.digits 10 c).length + c, by rw h1,
  have h4 : 6 * 10 ^ 5 + c = 4 * (10 * c + 6), by rw [h3, h2.right, h2.left],
  zify at *,
  exact helper_5_digit ↑c h4
end

/-
linarith fails on numbers this large, so this lemma spells out some of the arithmetic
that normally would be automated.
-/
lemma case_more_digits (c n : ℕ) (h1 : (nat.digits 10 c).length ≥ 6)
(h2 : n = 10 * c + 6 ∧ 6 * 10 ^ (nat.digits 10 c).length + c = 4 * n) : n ≥ 153846 :=
begin
   have h3 : c ≠ 0,
  { intro h4,
    have h5 : (nat.digits 10 c).length = 0, by simp [h4],
    exact case_0_digit c n h5 h2 },

  have h6 : 2 ≤ 10, by linarith,
  have h7 : 10 ^ (nat.digits 10 c).length ≤ 10 * c, from base_pow_length_digits_le 10 c h6 h3,
  have h8 : 10 ^ 6 ≤ 10 ^ (nat.digits 10 c).length, from (pow_le_iff_le_right h6).mpr h1,
  have h9 : 10 ^ 6 ≤ 10 * c, from le_trans h8 h7,
  norm_num at h9,
  have h10 : n = 10 * c + 6, from h2.left,
  have h11 : 10 * c ≤ n, from le.intro h10.symm,
  have h12 : 1000000 ≤ n, from le_trans h9 h11,
  have h13 : 153846 ≤ 1000000, by norm_num,
  exact le_trans h13 h12
end

/-
Now we combine these cases to show 153846 is the smallest solution.
-/

lemma satisfied_by_153846 : problem_predicate 153846 :=
by norm_num [problem_predicate, digit_recursion, of_digits]

lemma no_smaller_solutions (n : ℕ) (h1 : problem_predicate n) : n ≥ 153846 :=
begin
  cases (without_digits n h1) with c h2,
  have h3 : (nat.digits 10 c).length < 6 ∨ (nat.digits 10 c).length ≥ 6, by apply lt_or_ge,
  cases h3,
  interval_cases ((nat.digits 10 c).length),
  exact case_more_digits c n h3 h2,
  { exfalso, exact case_0_digit c n h h2 },
  { exfalso, exact case_1_digit c n h h2 },
  { exfalso, exact case_2_digit c n h h2 },
  { exfalso, exact case_3_digit c n h h2 },
  { exfalso, exact case_4_digit c n h h2 },
  have h4 : c = 15384, from case_5_digit c n h h2,
  have h5 : n = 10 * 15384 + 6, from eq.subst h4 h2.left,
  norm_num at h5,
  exact eq.ge h5
end

/-
The final part is converting from a statement about natural numbers, to the formulation
of the problem involving the minimum of a set.
-/

lemma solutions_nonempty : {n : ℕ | problem_predicate n}.nonempty :=
  have h : 153846 ∈ {n : ℕ | problem_predicate n}, from satisfied_by_153846,
  set.nonempty_of_mem h

theorem imo1962_q1 : is_least {n | problem_predicate n} 153846 :=
⟨satisfied_by_153846, no_smaller_solutions⟩



