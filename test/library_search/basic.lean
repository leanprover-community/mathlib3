/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.suggest -- No other imports, for fast testing

/- Turn off trace messages so they don't pollute the test build: -/
set_option trace.silence_library_search true
/- For debugging purposes, we can display the list of lemmas: -/
-- set_option trace.suggest true

namespace test.library_search

-- Check that `library_search` fails if there are no goals.
example : true :=
begin
  trivial,
  success_if_fail { library_search },
end

-- Verify that `library_search` solves goals via `solve_by_elim` when the library isn't
-- even needed.
example (P : Prop) (p : P) : P :=
by library_search
example (P : Prop) (p : P) (np : ¬P) : false :=
by library_search
example (X : Type) (P : Prop) (x : X) (h : Π x : X, x = x → P) : P :=
by library_search

example (α : Prop) : α → α :=
by library_search -- says: `exact id`

example (p : Prop) [decidable p] : (¬¬p) → p :=
by library_search -- says: `exact not_not.mp`

example (a b : Prop) (h : a ∧ b) : a :=
by library_search -- says: `exact h.left`

example (P Q : Prop) [decidable P] [decidable Q]: (¬ Q → ¬ P) → (P → Q) :=
by library_search -- says: `exact not_imp_not.mp`

example (a b : ℕ) : a + b = b + a :=
by library_search -- says: `exact add_comm a b`

example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by library_search -- says: `exact nat.mul_sub_left_distrib n m k`

example (n m k : ℕ) : n * m - n * k = n * (m - k) :=
by library_search -- says: `exact eq.symm (nat.mul_sub_left_distrib n m k)`

example {α : Type} (x y : α) : x = y ↔ y = x :=
by library_search -- says: `exact eq_comm`

example (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
by library_search -- says: `exact add_pos ha hb`

section synonym

-- Synonym `>` for `<` in another part of the goal
example (a b : ℕ) (ha : a > 0) (hb : 0 < b) : 0 < a + b :=
by library_search -- says: `exact add_pos ha hb`

example (a b : ℕ) (h : a ∣ b) (w : b > 0) : a ≤ b :=
by library_search -- says: `exact nat.le_of_dvd w h`

example (a b : ℕ) (h : a ∣ b) (w : b > 0) : b ≥ a :=
by library_search -- says: `exact nat.le_of_dvd w h`

-- A lemma with head symbol `¬` can be used to prove `¬ p` or `⊥`
example (a : ℕ) : ¬ (a < 0) := by library_search -- says `exact not_lt_bot`

example (a : ℕ) (h : a < 0) : false := by library_search -- says `exact not_lt_bot h`

-- An inductive type hides the constructor's arguments enough
-- so that `library_search` doesn't accidentally close the goal.
inductive P : ℕ → Prop
| gt_in_head {n : ℕ} : n < 0 → P n

-- This lemma with `>` as its head symbol should also be found for goals with head symbol `<`.
lemma lemma_with_gt_in_head (a : ℕ) (h : P a) : 0 > a := by { cases h, assumption }

-- This lemma with `false` as its head symbols should also be found for goals with head symbol `¬`.
lemma lemma_with_false_in_head (a b : ℕ) (h1 : a < b) (h2 : P a) : false :=
by { apply nat.not_lt_zero, cases h2, assumption }

example (a : ℕ) (h : P a) : 0 > a := by library_search -- says `exact lemma_with_gt_in_head a h`

example (a : ℕ) (h : P a) : a < 0 := by library_search -- says `exact lemma_with_gt_in_head a h`

example (a b : ℕ) (h1 : a < b) (h2 : P a) : false := by library_search
-- says `exact lemma_with_false_in_head a b h1 h2`

example (a b : ℕ) (h1 : a < b) : ¬ (P a) := by library_search!
-- says `exact lemma_with_false_in_head a b h1`

end synonym

-- We even find `iff` results:

example : ∀ P : Prop, ¬(P ↔ ¬P) :=
by library_search! -- says: `λ (a : Prop), (iff_not_self a).mp`

example {a b c : ℕ} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b :=
by library_search -- says `exact (nat.dvd_add_left h₁).mp h₂`

-- Checking examples from issue #2220
example {α : Sort*} (h : empty) : α :=
by library_search

example {α : Type*} (h : empty) : α :=
by library_search

def map_from_sum {A B C : Type} (f : A → C) (g : B → C) : (A ⊕ B) → C := by library_search

-- Test that we can set the transparency level in `apply`
-- to change how aggressively we unfold definitions while trying to apply lemmas.
lemma bind_singleton {α β} (x : α) (f : α → list β) : list.bind [x] f = f x :=
begin
  success_if_fail {
    library_search { md := tactic.transparency.reducible }, },
  library_search!,
end

constant f : ℕ → ℕ
axiom F (a b : ℕ) : f a ≤ f b ↔ a ≤ b

example (a b : ℕ) (h : a ≤ b) : f a ≤ f b := by library_search

-- Test #3432
theorem nonzero_gt_one (n : ℕ) : ¬ n = 0 → n ≥ 1 :=
by library_search!   -- `exact nat.pos_of_ne_zero`

end test.library_search
