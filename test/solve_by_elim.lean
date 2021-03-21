/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison
-/
import tactic.solve_by_elim
import tactic.rcases
import tactic.interactive

example {a b : Prop} (h₀ : a → b) (h₁ : a) : b :=
begin
  apply_assumption,
  apply_assumption,
end

example {X : Type} (x : X) : x = x :=
by solve_by_elim

example : true :=
by solve_by_elim

example {a b : Prop} (h₀ : a → b) (h₁ : a) : b :=
by solve_by_elim

example {α : Type} {a b : α → Prop} (h₀ : ∀ x : α, b x = a x) (y : α) : a y = b y :=
by solve_by_elim

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
by solve_by_elim

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
begin
  success_if_fail { solve_by_elim only [], },
  success_if_fail { solve_by_elim only [h₀], },
  solve_by_elim only [h₀, congr_fun]
end

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
by solve_by_elim [h₀]

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
begin
 success_if_fail { solve_by_elim [*, -h₀] },
 solve_by_elim [*]
end

example {α β : Type} (a b : α) (f : α → β) (i : function.injective f) (h : f a = f b) : a = b :=
begin
  success_if_fail { solve_by_elim only [i] },
  success_if_fail { solve_by_elim only [h] },
  solve_by_elim only [i,h]
end

@[user_attribute]
meta def ex : user_attribute := {
  name := `ex,
  descr := "An example attribute for testing solve_by_elim."
}

@[ex] def f : ℕ := 0

example : ℕ := by solve_by_elim [f]

example : ℕ :=
begin
  success_if_fail { solve_by_elim },
  success_if_fail { solve_by_elim [-f] with ex },
  solve_by_elim with ex,
end

example {α : Type} {p : α → Prop} (h₀ : ∀ x, p x) (y : α) : p y :=
begin
  apply_assumption,
end

open tactic

example : true :=
begin
  (do gs ← get_goals,
     set_goals [],
     success_if_fail `[solve_by_elim],
     set_goals gs),
  trivial
end

example {α : Type} (r : α → α → Prop) (f : α → α → α)
  (l : ∀ a b c : α, r a b → r a (f b c) → r a c)
  (a b c : α) (h₁ : r a b) (h₂ : r a (f b c)) : r a c :=
begin
  solve_by_elim,
end

-- Verifying that `solve_by_elim*` acts on all remaining goals.
example (n : ℕ) : ℕ × ℕ :=
begin
  split,
  solve_by_elim*,
end

-- Verifying that `solve_by_elim*` backtracks when given multiple goals.
example (n m : ℕ) (f : ℕ → ℕ → Prop) (h : f n m) : ∃ p : ℕ × ℕ, f p.1 p.2 :=
begin
  repeat { fsplit },
  solve_by_elim*,
end

example {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
begin
  apply le_trans,
  solve_by_elim { backtrack_all_goals := true },
end

-- test that metavariables created for implicit arguments don't get stuck
example (P : ℕ → Type) (f : Π {n : ℕ}, P n) : P 2 × P 3 :=
begin
  fsplit,
  solve_by_elim* only [f],
end

example : 6 = 6 ∧ [7] = [7] :=
begin
  split,
  solve_by_elim* only [@rfl _],
end

example (P Q R : Prop) : P ∧ Q → P ∧ Q :=
begin
  solve_by_elim [and.imp, id],
end

/-
We now test the `accept` feature of `solve_by_elim`.

Recall that the `accept` parameter has type `list expr → tactic unit`.
At each branch (not just leaf) of the backtracking search tree,
`accept` is invoked with the list of metavariables
reported by `get_goals` when `solve_by_elim` was called
(which by now may have been partially solved by previous `apply` steps),
and if it fails this branch of the search is ignored.

Non-leaf nodes of the search tree will contain metavariables,
so we can test using `expr.has_meta_var` when we're only interesting in
filtering complete solutions.

In this example, we only accept solutions that contain
a given subexpression.
-/
def solve_by_elim_use_b (a b : ℕ) : ℕ × ℕ × ℕ :=
begin
  split; [skip, split],
  (do
    b ← get_local `b,
    tactic.solve_by_elim
    { backtrack_all_goals := tt,
      -- We require that in some goal, the expression `b` is used.
      accept := (λ gs, gs.any_of (λ g, guard $ g.contains_expr_or_mvar b)) })
end

-- We verify that the solution did use `b`.
example : solve_by_elim_use_b 1 2 = (1, 1, 2) := rfl

-- Test that `solve_by_elim*`, which works on multiple goals,
-- successfully uses the relevant local hypotheses for each goal.
example (f g : ℕ → Prop) : (∃ k : ℕ, f k) ∨ (∃ k : ℕ, g k) ↔ ∃ k : ℕ, f k ∨ g k :=
begin
  dsimp at *,
  fsplit,
  rintro (⟨n, fn⟩ | ⟨n, gn⟩),
  swap 3,
  rintro ⟨n, hf | hg⟩,
  solve_by_elim* [or.inl, or.inr, Exists.intro] { max_depth := 20 },
end
