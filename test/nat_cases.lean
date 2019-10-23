/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import tactic.nat_cases

example (n : ℕ) : true :=
begin
  success_if_fail { nat_cases n },
  trivial
end

example (n : ℕ) (h : 2 ≤ n) : true :=
begin
  success_if_fail { nat_cases n },
  trivial
end

example (n : ℕ) (w₂ : n < 0) : false :=
by nat_cases n

example (n : ℕ) (w₂ : n < 1) : n * n = 0 :=
by nat_cases n; simp

example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
by nat_cases n; simp

example (n : ℕ) (w₁ : n > 2) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
by nat_cases n; simp

example (n : ℕ) (w₁ : n > 2) (w₂ : n ≤ 4) : n = 3 ∨ n = 4 :=
by nat_cases n; simp

example (n : ℕ) (w₁ : 2 < n) (w₂ : 4 ≥ n) : n = 3 ∨ n = 4 :=
by nat_cases n; simp

/-
Sadly, this one doesn't work, reporting:
  `deep recursion was detected at 'expression equality test'`
-/
-- example (n : ℕ) (w₁ : n > 1000000) (w₁ : n < 1000002) : n < 2000000 :=
-- begin
--   nat_cases n,
--   norm_num,
-- end
