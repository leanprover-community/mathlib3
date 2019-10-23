/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import tactic.nat_cases

example (n : ℕ) (h₁ : n ≥ 3) (h₂ : n < 5) : n = 3 ∨ n = 4 :=
begin
  nat_cases n,
end
