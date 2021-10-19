/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/

import tactic.rcases

universe u
variables {α β γ : Type u}

example (x : α × β × γ) : true :=
begin
  rcases x with ⟨a, b, c⟩,
  { guard_hyp a : α,
    guard_hyp b : β,
    guard_hyp c : γ,
    trivial }
end

example (x : α × β × γ) : true :=
begin
  rcases x with ⟨a, ⟨-, c⟩⟩,
  { guard_hyp a : α,
    success_if_fail { guard_hyp x_snd_fst : β },
    guard_hyp c : γ,
    trivial }
end

example (x : (α × β) × γ) : true :=
begin
  rcases x with ⟨⟨a:α, b⟩, c⟩,
  { guard_hyp a : α,
    guard_hyp b : β,
    guard_hyp c : γ,
    trivial }
end

example : inhabited α × option β ⊕ γ → true :=
begin
  rintro (⟨⟨a⟩, _ | b⟩ | c),
  { guard_hyp a : α, trivial },
  { guard_hyp a : α, guard_hyp b : β, trivial },
  { guard_hyp c : γ, trivial }
end

example : cond ff ℕ ℤ → cond tt ℤ ℕ → (ℕ ⊕ unit) → true :=
begin
  rintro (x y : ℤ) (z | u),
  { guard_hyp x : ℤ, guard_hyp y : ℤ, guard_hyp z : ℕ, trivial },
  { guard_hyp x : ℤ, guard_hyp y : ℤ, guard_hyp u : unit, trivial }
end

example (x y : ℕ) (h : x = y) : true :=
begin
  rcases x with _|⟨⟩|z,
  { guard_hyp h : nat.zero = y, trivial },
  { guard_hyp h : nat.succ nat.zero = y, trivial },
  { guard_hyp z : ℕ,
    guard_hyp h : z.succ.succ = y, trivial },
end

-- from equiv.sum_empty
example (s : α ⊕ empty) : true :=
begin
  rcases s with _ | ⟨⟨⟩⟩,
  { guard_hyp s : α, trivial }
end

example : true :=
begin
  obtain ⟨n : ℕ, h : n = n, -⟩ : ∃ n : ℕ, n = n ∧ true,
  { existsi 0, simp },
  guard_hyp n : ℕ,
  guard_hyp h : n = n,
  success_if_fail {assumption},
  trivial
end

example : true :=
begin
  obtain : ∃ n : ℕ, n = n ∧ true,
  { existsi 0, simp },
  trivial
end

example : true :=
begin
  obtain (h : true) | ⟨⟨⟩⟩ : true ∨ false,
  { left, trivial },
  guard_hyp h : true,
  trivial
end

example : true :=
begin
  obtain h | ⟨⟨⟩⟩ : true ∨ false := or.inl trivial,
  guard_hyp h : true,
  trivial
end

example : true :=
begin
  obtain ⟨h, h2⟩ := and.intro trivial trivial,
  guard_hyp h : true,
  guard_hyp h2 : true,
  trivial
end

example : true :=
begin
  success_if_fail {obtain ⟨h, h2⟩},
  trivial
end

example (x y : α × β) : true :=
begin
  rcases ⟨x, y⟩ with ⟨⟨a, b⟩, c, d⟩,
  { guard_hyp a : α,
    guard_hyp b : β,
    guard_hyp c : α,
    guard_hyp d : β,
    trivial }
end

example (x y : α ⊕ β) : true :=
begin
  obtain ⟨a|b, c|d⟩ := ⟨x, y⟩,
  { guard_hyp a : α, guard_hyp c : α, trivial },
  { guard_hyp a : α, guard_hyp d : β, trivial },
  { guard_hyp b : β, guard_hyp c : α, trivial },
  { guard_hyp b : β, guard_hyp d : β, trivial },
end

example {i j : ℕ} : (Σ' x, i ≤ x ∧ x ≤ j) → i ≤ j :=
begin
  intro h,
  rcases h' : h with ⟨x,h₀,h₁⟩,
  guard_hyp h' : h = ⟨x,h₀,h₁⟩,
  apply le_trans h₀ h₁,
end

protected def set.foo {α β} (s : set α) (t : set β) : set (α × β) := ∅

example {α} (V : set α) (w : true → ∃ p, p ∈ (V.foo V) ∩ (V.foo V)) : true :=
begin
  obtain ⟨a, h⟩ : ∃ p, p ∈ (V.foo V) ∩ (V.foo V) := w trivial,
  trivial,
end

example (n : ℕ) : true :=
begin
  obtain one_lt_n | n_le_one : 1 < n + 1 ∨ n + 1 ≤ 1 := nat.lt_or_ge 1 (n + 1),
  trivial, trivial,
end

example (n : ℕ) : true :=
begin
  obtain one_lt_n | (n_le_one : n + 1 ≤ 1) := nat.lt_or_ge 1 (n + 1),
  trivial, trivial,
end

example (h : ∃ x : ℕ, x = x ∧ 1 = 1) : true :=
begin
  rcases h with ⟨-, _⟩,
  (do lc ← tactic.local_context, guard lc.empty),
  trivial
end

example (h : ∃ x : ℕ, x = x ∧ 1 = 1) : true :=
begin
  rcases h with ⟨-, _, h⟩,
  (do lc ← tactic.local_context, guard (lc.length = 1)),
  guard_hyp h : 1 = 1,
  trivial
end

example (h : true ∨ true ∨ true) : true :=
begin
  rcases h with -|-|-,
  iterate 3 {
    (do lc ← tactic.local_context, guard lc.empty),
    trivial },
end

example : bool → false → true
| ff := by rintro ⟨⟩
| tt := by rintro ⟨⟩

open tactic
meta def test_rcases_hint (s : string) (num_goals : ℕ) (depth := 5) : tactic unit :=
do change `(true),
  h ← get_local `h,
  pat ← rcases_hint ```(h) depth,
  p ← pp pat,
  guard (p.to_string = s) <|> fail format!"got '{p.to_string}', expected: '{s}'",
  gs ← get_goals,
  guard (gs.length = num_goals) <|> fail format!"there are {gs.length} goals remaining",
  all_goals triv $> ()

example {α} (h : ∃ x : α, x = x) := by test_rcases_hint "⟨h_w, ⟨⟩⟩" 1
example (h : true ∨ true ∨ true) := by test_rcases_hint "⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩" 3
example (h : ℕ) := by test_rcases_hint "_ | _ | h" 3 2
example {p} (h : (p ∧ p) ∨ (p ∧ p)) :=
by test_rcases_hint "⟨h_left, h_right⟩ | ⟨h_left, h_right⟩" 2
example {p} (h : (p ∧ p) ∨ (p ∧ (p ∨ p))) :=
by test_rcases_hint "⟨h_left, h_right⟩ | ⟨h_left, h_right | h_right⟩" 3
example {p} (h : p ∧ (p ∨ p)) :=
by test_rcases_hint "⟨h_left, h_right | h_right⟩" 2
example (h : 0 < 2) := by test_rcases_hint "_ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩" 1
example (h : 3 < 2) := by test_rcases_hint "_ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩" 0
example (h : 3 < 0) := by test_rcases_hint "⟨⟩" 0
example (h : false) := by test_rcases_hint "⟨⟩" 0
example (h : true) := by test_rcases_hint "⟨⟩" 1
example {α} (h : list α) := by test_rcases_hint "_ | ⟨h_hd, _ | ⟨h_tl_hd, h_tl_tl⟩⟩" 3 2
example {α} (h : (α ⊕ α) × α) := by test_rcases_hint "⟨h_fst | h_fst, h_snd⟩" 2 2

inductive foo (α : Type) : ℕ → Type
| zero : foo 0
| one (m) : α → foo m

example {α} (h : foo α 0) : true := by test_rcases_hint "_ | ⟨_, h_ᾰ⟩" 2
example {α} (h : foo α 1) : true := by test_rcases_hint "_ | ⟨_, h_ᾰ⟩" 1
example {α n} (h : foo α n) : true := by test_rcases_hint "_ | ⟨n, h_ᾰ⟩" 2 1

example {α} (V : set α) (h : ∃ p, p ∈ (V.foo V) ∩ (V.foo V)) :=
by test_rcases_hint "⟨⟨h_w_fst, h_w_snd⟩, ⟨⟩⟩" 0
