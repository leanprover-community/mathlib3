/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/

import data.nat.digits

/-!
# IMO 1960 Q1

Determine all three-digit numbers $N$ having the property that $N$ is divisible by 11, and
$\dfrac{N}{11}$ is equal to the sum of the squares of the digits of $N$.

Since Lean doesn't have a way to directly express problem statements of the form
"Determine all X satisfying Y", we express two predicates where proving that one implies the
other is equivalent to solving the problem. A human solver also has to discover the
second predicate.

The strategy here is roughly brute force, checking the possible multiples of 11.
-/

open nat

def sum_of_squares (L : list ℕ) : ℕ := (L.map (λ x, x * x)).sum

def problem_predicate (n : ℕ) : Prop :=
(nat.digits 10 n).length = 3 ∧ 11 ∣ n ∧ n / 11 = sum_of_squares (nat.digits 10 n)

def solution_predicate (n : ℕ) : Prop := n = 550 ∨ n = 803

/-
Proving that three digit numbers are the ones in [100, 1000).
-/

lemma not_zero {n : ℕ} (h1 : problem_predicate n) : n ≠ 0 :=
have h2 : nat.digits 10 n ≠ list.nil, from list.ne_nil_of_length_eq_succ h1.left,
digits_ne_nil_iff_ne_zero.mp h2

lemma ge_100 {n : ℕ} (h1 : problem_predicate n) : 100 ≤ n :=
have h2 : 10^3 ≤ 10 * n, begin
  rw ← h1.left,
  refine nat.base_pow_length_digits_le 10 n _ (not_zero h1),
  simp,
end,
by linarith

lemma lt_1000 {n : ℕ} (h1 : problem_predicate n) : n < 1000 :=
have h2 : n < 10^3, begin
  rw ← h1.left,
  refine nat.lt_base_pow_length_digits _,
  simp,
end,
by linarith

/-
We do an exhaustive search to show that all results are covered by `solution_predicate`.
-/

def search_up_to (c n : ℕ) : Prop :=
n = c * 11 ∧ ∀ m : ℕ, m < n → problem_predicate m → solution_predicate m

lemma search_up_to_start : search_up_to 9 99 := ⟨rfl, λ n h p, by linarith [ge_100 p]⟩

lemma search_up_to_step {c n} (H : search_up_to c n)
  {c' n'} (ec : c + 1 = c') (en : n + 11 = n')
  {l} (el : nat.digits 10 n = l)
  (H' : c = sum_of_squares l → c = 50 ∨ c = 73) :
  search_up_to c' n' :=
begin
  subst ec, subst en, subst el,
  obtain ⟨rfl, H⟩ := H,
  refine ⟨by ring, λ m l p, _⟩,
  obtain ⟨h₁, ⟨m, rfl⟩, h₂⟩ := id p,
  by_cases h : 11 * m < c * 11, { exact H _ h p },
  have : m = c, {linarith}, subst m,
  rw [nat.mul_div_cancel_left _ (by norm_num : 11 > 0), mul_comm] at h₂,
  refine (H' h₂).imp _ _; {rintro rfl, norm_num}
end

lemma search_up_to_end {c} (H : search_up_to c 1001)
  {n : ℕ} (ppn : problem_predicate n) : solution_predicate n :=
H.2 _ (by linarith [lt_1000 ppn]) ppn

lemma right_direction {n : ℕ} : problem_predicate n → solution_predicate n :=
begin
  have := search_up_to_start,
  iterate 82
  { replace := search_up_to_step this (by norm_num1; refl) (by norm_num1; refl)
      (by norm_num1; refl) dec_trivial },
  exact search_up_to_end this
end

/-
Now we just need to prove the equivalence, for the precise problem statement.
-/

lemma left_direction (n : ℕ) (spn : solution_predicate n) : problem_predicate n :=
by rcases spn with (rfl | rfl); norm_num [problem_predicate, sum_of_squares]

theorem imo1960_q1 (n : ℕ) : problem_predicate n ↔ solution_predicate n :=
⟨right_direction, left_direction n⟩
