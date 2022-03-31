/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.suggest
import data.nat.basic

namespace test.library_search

/- Turn off trace messages so they don't pollute the test build: -/
set_option trace.silence_library_search true
/- For debugging purposes, we can display the list of lemmas: -/
-- set_option trace.suggest true

def lt_one (n : ℕ) := n < 1
lemma zero_lt_one (n : ℕ) (h : n = 0) : lt_one n := by subst h; dsimp [lt_one]; simp

-- Verify that calls to solve_by_elim to discharge subgoals use `rfl`
example : lt_one 0 :=
by library_search


example {n m : ℕ} (h : m < n) : m ≤ n - 1 :=
by library_search -- says: `exact nat.le_pred_of_lt h`

example (a b : ℕ) : 0 < a → 0 < b → 0 < a + b :=
by library_search -- says: `exact add_pos`

section synonym

-- Synonym `>` for `<` in the goal
example (a b : ℕ) : 0 < a → 0 < b → a + b > 0 :=
by library_search -- says: `exact add_pos`

-- Synonym `>` for `<` in another part of the goal
example (a b : ℕ) : a > 0 → 0 < b → 0 < a + b :=
by library_search -- says: `exact add_pos`

end synonym


example {a b c : ℕ} (ha : a > 0) (w : b ∣ c) : a * b ∣ a * c :=
by library_search -- exact mul_dvd_mul_left a w

-- We have control of how `library_search` uses `solve_by_elim`.

-- In particular, we can add extra lemmas to the `solve_by_elim` step
-- (i.e. for `library_search` to use to attempt to discharge subgoals
-- after successfully applying a lemma from the library.)
example {a b c d: nat} (h₁ : a < c) (h₂ : b < d) : max (c + d) (a + b) = (c + d) :=
begin
  library_search [add_lt_add], -- Says: `exact max_eq_left_of_lt (add_lt_add h₁ h₂)`
end

-- We can also use attributes:
meta def ex_attr : user_attribute := {
  name := `ex,
  descr := "A lemma that should be applied by `library_search` when discharging subgoals."
}

run_cmd attribute.register ``ex_attr

attribute [ex] add_lt_add

example {a b c d: nat} (h₁ : a < c) (h₂ : b < d) : max (c + d) (a + b) = (c + d) :=
begin
  library_search with ex, -- Says: `exact max_eq_left_of_lt (add_lt_add h₁ h₂)`
end

example (a b : ℕ) (h : 0 < b) : (a * b) / b = a :=
by library_search -- Says: `exact nat.mul_div_left a h`

example (a b : ℕ) (h : b ≠ 0) : (a * b) / b = a :=
begin
  success_if_fail { library_search },
  library_search [pos_iff_ne_zero.mpr],
end

end test.library_search
