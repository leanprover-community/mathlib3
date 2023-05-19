/-
Copyright (c) 2023 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
import data.nat.factorial.basic
import algebra.big_operators.order
import tactic.ring
/-!
# Double factorials

This file defines the double factorial,
  `n‼ := n * (n - 2) * (n - 4) * ...`.

## Main declarations

* `nat.double_factorial`: The double factorial.
-/

open_locale nat
namespace nat

/-- `nat.double_factorial n` is the double factorial of `n`. -/
@[simp] def double_factorial : ℕ → ℕ
| 0       := 1
| 1       := 1
| (k + 2) := (k + 2) * double_factorial k

-- This notation is `\!!` not two !'s
localized "notation (name := nat.double_factorial) n `‼`:10000 := nat.double_factorial n" in nat

lemma double_factorial_add_two (n : ℕ) : (n + 2)‼ = (n + 2) * n‼ := rfl

lemma double_factorial_add_one (n : ℕ) : (n + 1)‼ = (n + 1) * (n - 1)‼ := by { cases n; refl }

lemma factorial_eq_mul_double_factorial : ∀ (n : ℕ), (n + 1)! = (n + 1)‼ * n‼
| 0 := rfl
| (k + 1) := begin
  rw [double_factorial_add_two, factorial, factorial_eq_mul_double_factorial,
      mul_comm _ (k‼), mul_assoc]
end

lemma double_factorial_two_mul :
  ∀ (n : ℕ), (2 * n)‼ = 2^n * n!
| 0       := rfl
| (n + 1) := begin
  rw [mul_add, mul_one, double_factorial_add_two, factorial, pow_succ,
      double_factorial_two_mul, succ_eq_add_one],
  ring,
end

open_locale big_operators

lemma double_factorial_eq_prod_even :
  ∀ (n : ℕ), (2 * n)‼ = ∏ i in finset.range n, (2 * (i + 1))
| 0       := rfl
| (n + 1) := begin
  rw [finset.prod_range_succ, ← double_factorial_eq_prod_even, mul_comm (2 * n)‼,
      (by ring : 2 * (n + 1) = 2 * n + 2)],
  refl,
end

lemma double_factorial_eq_prod_odd :
  ∀ (n : ℕ), (2 * n + 1)‼ = ∏ i in finset.range n, (2 * (i + 1) + 1)
| 0       := rfl
| (n + 1) := begin
  rw [finset.prod_range_succ, ← double_factorial_eq_prod_odd, mul_comm (2 * n + 1)‼,
      (by ring : 2 * (n + 1) + 1 = (2 * n + 1) + 2)],
  refl,
end

end nat
