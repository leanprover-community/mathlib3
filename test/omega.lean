/-
Test cases for omega. Most of the examples are from John Harrison's
Handbook of Practical Logic and Automated Reasoning.
-/

import data.fintype
import tactic.omega

example (n : ℤ) : n - 1 ≠ n := by omega
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
example (a b : ℕ) (h : a < b + 1) (ha : a.prime) : a ≤ b := by omega
example (a b c : ℕ) (h : a < b + 1) (ha : c.prime) : a ≤ b := by omega
example (a b : ℕ) (h : a < b + 1) (p : fin a) : a ≤ b := by omega
example : nat.zero = nat.zero := by omega
example : 3 < 4 := by omega
example {X : Type} [fintype X] (n k : ℕ) (hk : k + 1 ≤ n) : n - k = n - (k + 1) + 1 := by omega
example (n : ℕ) (G_C G_L : list ℤ) (hG : G_C.length + G_L.length = n + 1)
  (iv : ℕ) (hi : iv < G_C.length) : iv + (G_C.length - iv - 1) + G_L.length = n := by omega

/-
Use `omega T` to specify the domain, where `T = int` or `T = nat`.
-/
example (i : int) (n : nat) (h1 : n = 0) (h2 : i < i) : false := by omega int
example (i : int) (n : nat) (h1 : i = 0) (h2 : n < n) : false := by omega nat

/-
Use `omega manual T` to disable automatic reverts, where `T = int` or `T = nat`.
-/
example (x y z w : int) (h1 : 3 * y ≥ x) (h2 : z > 19 * w) : 3 * x ≤ 9 * y :=
by {revert h1, omega manaul int}
example (n : nat) (h1 : n < 34) (i : int) (h2 : i * 9 = -72) : i = -8 :=
by {revert h2, omega manual int}
