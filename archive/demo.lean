/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/

import data.nat.parity
import algebra.big_operators.intervals
import tactic.ring
open finset
open_locale big_operators





-- # Example 1

example : ∀ m n : ℤ, odd m → odd n → odd (m * n) :=
begin
  sorry,
end





-- # Example 2

example (n : ℕ) : ∑ i in range (n + 1), 2 * i = n * (n + 1) :=
begin
  sorry,
end
