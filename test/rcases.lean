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
