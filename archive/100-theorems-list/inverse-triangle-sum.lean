/-
Copyright (c) 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark,
<<<<<<< HEAD
Solving problem 42 on the list of 100 theorems.
=======

Solving problem 42 on the list of 100 theorems, which involves a "telescoping" sum.
>>>>>>> fbfdbe1c18421daedfd6e8884c763b3098265e6c
-/
import tactic
import algebra.big_operators
import data.real.basic

/-!
The problem is referred to as "Sum of the Reciprocals of the Triangular Numbers" on the 100 theorems list.

We interpret "triangular numbers" as naturals of the form k(k+1)/2 for natural k. We prove that the sum of the first n triangular numbers is equal 2 - 2/n.

## Tags

discrete_sum
-/

lemma inverse_triangle_sum
(n : ℕ) :
(finset.range n).sum (λ x, (2 : ℚ) / (x * (x + 1))) = if n ≤ 1 then 0 else 2 - (2 : ℚ) / n :=
begin
rw finset.sum_range_induction,
  {rw if_pos, norm_num},
intro n,

by_cases h0 : n = 0,
  {rw [h0, if_pos, if_pos], ring,
    norm_num, norm_num},

by_cases h1 : n = 1,
  {rw [h1, if_neg, if_pos], ring,
    norm_num, norm_num,},

-- we're going to do arithmetic where n-1, n, and n+1 all appear in denominators, so let's show that's okay
have n0 : ( n : ℚ) ≠ 0 := by {norm_cast, exact h0}, clear h0,
have n1 : ( (n + 1) : ℚ) ≠ 0 := by {norm_cast, omega},
have nn1 : ( n - 1: ℚ) ≠ 0,
  {intro h, revert h1, rw [imp_false, not_not],
  apply_fun (λ x, x + 1) at h,
  simp only [sub_add_cancel, zero_add] at h,
  norm_cast at h, exact h},

-- let's clear our if-then-else
rw if_neg, swap,
  {revert h1 n0, norm_cast, omega},
rw if_neg, swap,
  {revert n0, norm_cast, omega},
clear h1,

-- let's leave ℕ now
have coe_elim : ∃ x : ℚ, (n : ℚ) = x, simp only [exists_eq'],
cases coe_elim with x coe_elim,
simp only [one_div_eq_inv, add_sub_cancel, nat.cast_add, nat.cast_one],
rw coe_elim at *,
clear coe_elim n,

-- now that we're morally in (units ℚ), our tactics can do the arithmetic
field_simp [nn1, n0, n1], ring,
end
