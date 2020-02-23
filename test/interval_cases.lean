/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import tactic.interval_cases

example (n : ℕ) : true :=
begin
  success_if_fail { interval_cases n },
  trivial
end

example (n : ℕ) (h : 2 ≤ n) : true :=
begin
  success_if_fail { interval_cases n },
  trivial
end

example (n : ℕ) (w₂ : n < 0) : false :=
by interval_cases n

example (n : ℕ) (w₂ : n < 1) : n = 0 :=
by { interval_cases n, refl }

-- @[simp] lemma nat.bot_eq_zero : (⊥ : ℕ) = 0 := rfl
attribute [simp] bot_eq_zero

example (n : ℕ) (w₂ : n < 2) : n = 0 ∨ n = 1 :=
by { interval_cases n, simp, simp, }

example (n : ℕ) (w₁ : 1 ≤ n) (w₂ : n < 3) : n = 1 ∨ n = 2 :=
by { interval_cases n, simp, simp, }

def foo : lattice.order_bot ℕ := by apply_instance
instance : lattice.has_bot ℕ+ :=
{ bot := 1 }
instance : lattice.order_bot ℕ+ :=
{ bot_le := λ a, a.property,
  ..(by apply_instance : lattice.has_bot ℕ+),
  ..(by apply_instance : partial_order ℕ+) }

example (n : ℕ+) (w₂ : n < 1) : false :=
by { interval_cases n }

@[simp] lemma pnat.bot_eq_zero : (⊥ : ℕ+) = 1 := rfl

example (n : ℕ+) (w₂ : n < 2) : n = 1 :=
by { interval_cases n, refl, }

example (n : ℕ+) (w₂ : n < 3) : n = 1 ∨ n = 2 :=
by { interval_cases n, { left, refl }, { right, refl }, }

example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
by { interval_cases n, simp, simp, }

example (n : ℕ) (h : n = max (max ⊥ 2) 3 + 1) : true :=
begin
 conv at h { norm_num, },
 trivial,
end

example (n : ℕ) (w₀ : n ≥ 2) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
by { interval_cases n, norm_num, norm_num, }

example (n : ℕ) (w₁ : n > 2) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
by { interval_cases n, simp, simp, }

example (n : ℕ) (w₁ : n > 2) (w₂ : n ≤ 4) : n = 3 ∨ n = 4 :=
by { interval_cases n, simp, simp, }

example (n : ℕ) (w₁ : 2 < n) (w₂ : 4 ≥ n) : n = 3 ∨ n = 4 :=
by { interval_cases n, simp, simp, }

example (n : ℕ) (w₁ : n % 3 < 1) : n % 3 = 0 :=
by { interval_cases n % 3, assumption }

/-
Sadly, this one doesn't work, reporting:
  `deep recursion was detected at 'expression equality test'`
-/
example (n : ℕ) (w₁ : n > 1000000) (w₁ : n < 1000002) : n < 2000000 :=
begin
  interval_cases n,
  norm_num,
end

example (n : ℕ) (h1 : 4 ≤ n) (h2 : n < 10) : n < 20 :=
begin
  interval_cases_using h1 h2,
  all_goals {norm_num}
end

example (z : ℤ) (h1 : z ≥ -3) (h2 : z < 2) : z < 20 :=
begin
  interval_cases_using h1 h2,
  all_goals {norm_num}
end

example (n : ℕ) (h1 : 4 < n) (h2 : n ≤ 6) : n < 20 :=
begin
  interval_cases n,
  guard_target 5 < 20, norm_num,
  guard_target 6 < 20, norm_num,
end

example (n : ℕ+) (h1 : 4 ≤ n) (h2 : n < 5) : n = 4 :=
begin
  interval_cases n,
  apply pnat.eq, -- TODO make this an extensionality lemma?
  norm_num,      -- TOOD should norm_num just work on pnat?
end

example (z : ℤ) (h1 : z ≥ -3) (h2 : z < 2) : z < 20 :=
begin
  interval_cases z,
  guard_target (-3 : ℤ) < 20, norm_num,
  guard_target (-2 : ℤ) < 20, norm_num,
  guard_target (-1 : ℤ) < 20, norm_num,
  guard_target (0 : ℤ) < 20, norm_num,
  guard_target (1 : ℤ) < 20, norm_num,
end
