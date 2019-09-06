/-
Test cases for omega. Most of the examples are from John Harrison's
Handbook of Practical Logic and Automated Reasoning.
-/

import tactic.omega

example (x : int) : (x = 5 ∨ x = 7) → 2 < x := by omega
example (x : int) : x ≤ -x → x ≤ 0 := by omega
example : ∀ x y : int, (x ≤ 5 ∧ y ≤ 3) → x + y ≤ 8 := by omega
example : ∀ (x y z : int), x < y → y < z → x < z := by omega
example (x y z : int) : x - y ≤ x - z → z ≤ y:= by omega
example (x : int) (h1 : x = -5 ∨ x = 7) (h2 : x = 0) : false := by omega
example : ∀ x : int, 31 * x > 0 → x > 0 := by omega
example (x y : int) : (-x - y < x - y) → (x - y < x + y) → (x > 0 ∧ y > 0) := by omega
example : ∀ (x : int), (x ≥ -1 ∧ x ≤ 1) → (x = -1 ∨ x = 0 ∨ x = 1) := by omega
example : ∀ (x : int), 5 * x = 5 → x = 1 := by omega
example (x y : int) : ∀ z w v : int, x = y → y = z → x = z := by omega
example : ∀ x : int, x < 349 ∨ x > 123 := by omega
example : ∀ x y : int, x ≤ 3 * y → 3 * x ≤ 9 * y := by omega
example (x : int) (h1 : x < 43 ∧ x > 513) : false := by omega
example (x y z w : int) : x ≤ y → y ≤ z → z ≤ w → x ≤ w:= by omega
example (x y z : int) : ∀ w v : int, 100 = x → x = y → y = z → z = w → w = v → v = 100 := by omega

example (x : nat) : 31 * x > 0 → x > 0 := by omega
example (x y : nat) : (x ≤ 5 ∧ y ≤ 3) → x + y ≤ 8 := by omega
example : ∀ (x y z y : nat), ¬(2 * x + 1 = 2 * y) := by omega
example : ∀ (x y : nat),  x > 0 → x + y > 0 := by omega
example : ∀ (x : nat),  x < 349 ∨ x > 123 := by omega
example  : ∀ (x y : nat), (x = 2 ∨ x = 10) → (x = 3 * y) → false := by omega
example (x y : nat) :  x ≤ 3 * y → 3 * x ≤ 9 * y := by omega
example (x y z : nat) : (x ≤ y) → (z > y) → (x - z = 0) := by omega
example (x y z : nat) : x - 5 > 122 → y ≤ 127 → y < x := by omega
example : ∀ (x y : nat), x ≤ y ↔ x - y = 0 := by omega
example (k : nat) (h : 1 * 1 + 1 * 1 + 1 = 1 * 1 * k) : k = 3 := by omega

/-
Use `omega manual` to disable automatic reverts,
and `omega int` or `omega nat` to specify the domain.
-/
example (i : int) (n : nat) (h1 : n = 0) (h2 : i < i) : false := by omega int
example (i : int) (n : nat) (h1 : i = 0) (h2 : n < n) : false := by omega nat
example (x y z w : int) (h1 : 3 * y ≥ x) (h2 : z > 19 * w) : 3 * x ≤ 9 * y :=
by {revert h1 x y, omega manual}
example (n : nat) (h1 : n < 34) (i : int) (h2 : i * 9 = -72) : i = -8 :=
by {revert h2 i, omega manual int}
