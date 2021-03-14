/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/

import data.nat.parity
import data.real.basic
import algebra.big_operators.intervals
import tactic.ring
open finset set
open_locale big_operators


-- # Example 1

example : ∀ m n : ℕ, odd m → odd n → odd (m * n) :=
begin
  sorry,
end







-- # Example 2

--example (n : ℕ) (f : ℕ → ℕ) : ∑ i in range n.succ, f i = ∑ i in range n, f i + f n := by library_search

example (n : ℕ) : ∑ i in range (n + 1), 2 * i = n * (n + 1) :=
begin
  sorry,
end







-- # Example 3

example (s t : set ℝ) (h : ∀ x, x ∈ s → x ∉ t) : s ∩ t = ∅ :=
begin
  sorry,
end
