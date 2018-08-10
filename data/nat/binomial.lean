/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.nat.choose algebra.big_operators

open nat finset

/-- The binomial theorem -/
theorem add_pow {α : Type*} [comm_semiring α] (x y : α) : ∀ n : ℕ,
    (x + y) ^ n = (range (succ n)).sum (λ m, x ^ m * y ^ (n - m) * choose n m)
| 0        := by simp
| (succ n) :=
have h₁ : x * (x ^ n * y ^ (n - n) * choose n n) =
    x ^ succ n * y ^ (succ n - succ n) * choose (succ n) (succ n),
  by simp [_root_.pow_succ, mul_assoc, mul_comm, mul_left_comm],
have  h₂ : y * (x^0 * y^(n - 0) * choose n 0) = x^0 * y^(succ n - 0) * choose (succ n) 0,
  by simp [_root_.pow_succ, mul_assoc, mul_comm, mul_left_comm],
have h₃ : (range n).sum (λ m, x * (x ^ m * y ^ (n - m) * choose n m) + y *
    (x ^ succ m * y ^ (n - succ m) * choose n (succ m)))
    = (range n).sum (λ m, x ^ succ m * y ^ (succ n - succ m) * ↑(choose (succ n) (succ m))),
  from finset.sum_congr rfl $ λ m hm,
    begin
      simp only [mul_assoc, mul_left_comm y, mul_left_comm (y ^ (n - succ m)), mul_comm y],
      rw [← _root_.pow_succ', add_one, ← succ_sub (mem_range.1 hm)],
      simp [choose_succ_succ, mul_comm, mul_assoc, mul_left_comm, add_mul, mul_add, _root_.pow_succ]
    end,
by rw [_root_.pow_succ, add_pow, add_mul, finset.mul_sum, finset.mul_sum, sum_range_succ, sum_range_succ',
    sum_range_succ, sum_range_succ', add_assoc, ← add_assoc ((range n).sum _),
    ← finset.sum_add_distrib, h₁, h₂, h₃]