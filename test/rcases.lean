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
  { guard_hyp a := α,
    guard_hyp b := β,
    guard_hyp c := γ,
    trivial }
end

example (x : α × β × γ) : true :=
begin
  rcases x with ⟨a, ⟨b, c⟩⟩,
  { guard_hyp a := α,
    guard_hyp b := β,
    guard_hyp c := γ,
    trivial }
end

example (x : (α × β) × γ) : true :=
begin
  rcases x with ⟨⟨a, b⟩, c⟩,
  { guard_hyp a := α,
    guard_hyp b := β,
    guard_hyp c := γ,
    trivial }
end

example : inhabited α × option β ⊕ γ → true :=
begin
  rintro (⟨⟨a⟩, _ | b⟩ | c),
  { guard_hyp a := α, trivial },
  { guard_hyp a := α, guard_hyp b := β, trivial },
  { guard_hyp c := γ, trivial }
end

example (x y : ℕ) (h : x = y) : true :=
begin
  rcases x with _|⟨⟩|z,
  { guard_hyp h := nat.zero = y, trivial },
  { guard_hyp h := nat.succ nat.zero = y, trivial },
  { guard_hyp z := ℕ,
    guard_hyp h := z.succ.succ = y, trivial },
end

-- from equiv.sum_empty
example (s : α ⊕ empty) : true :=
begin
  rcases s with _ | ⟨⟨⟩⟩,
  { guard_hyp s := α, trivial }
end

example : true :=
begin
  obtain ⟨n, h, f⟩ : ∃ n : ℕ, n = n ∧ true,
  { existsi 0, simp },
  guard_hyp n := ℕ,
  guard_hyp h := n = n,
  guard_hyp f := true,
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
  obtain h | ⟨⟨⟩⟩ : true ∨ false,
  { left, trivial },
  guard_hyp h := true,
  trivial
end

example : true :=
begin
  obtain h | ⟨⟨⟩⟩ : true ∨ false := or.inl trivial,
  guard_hyp h := true,
  trivial
end

example : true :=
begin
  obtain ⟨h, h2⟩ := and.intro trivial trivial,
  guard_hyp h := true,
  guard_hyp h2 := true,
  trivial
end

example : true :=
begin
  success_if_fail {obtain ⟨h, h2⟩},
  trivial
end
