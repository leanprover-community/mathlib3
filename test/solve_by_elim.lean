/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison
-/
import tactic data.set.lattice data.prod data.vector
       tactic.rewrite data.stream.basic

example {a b : Prop} (h₀ : a → b) (h₁ : a) : b :=
begin
  apply_assumption,
  apply_assumption,
end

example {a b : Prop} (h₀ : a → b) (h₁ : a) : b :=
by solve_by_elim

example {α : Type} {a b : α → Prop} (h₀ : ∀ x : α, b x = a x) (y : α) : a y = b y :=
by solve_by_elim

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
by solve_by_elim

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
begin
  success_if_fail { solve_by_elim only [] },
  success_if_fail { solve_by_elim only [h₀] },
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

-- Verifying that solve_by_elim behaves as expected in the presence of multiple goals.
example (n : ℕ) : ℕ × ℕ :=
begin
  split,
  solve_by_elim,
  solve_by_elim
end

example {P Q : Prop} (h : P ↔ Q) (h : P) : Q :=
begin
  solve_by_elim
end

example {P Q : Prop} (h : P ↔ Q) (h : Q) : P :=
begin
  solve_by_elim
end

example {a b c : ℕ} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b :=
begin
  solve_by_elim [nat.dvd_add_iff_left],
end

