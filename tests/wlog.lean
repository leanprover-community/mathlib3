/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic

example {a b : Prop} (h₀ : a → b) (h₁ : a) : b :=
begin
  apply_assumption,
  apply_assumption,
end

example {a b : Prop} (h₀ : a → b) (h₁ : a) : b :=
by solve_by_elim

example {α : Type} {p : α → Prop} (h₀ : ∀ x, p x) (y : α) : p y :=
begin
  apply_assumption,
end

section tauto₀
variables p q r : Prop
variables h : p ∧ q ∨ p ∧ r
include h
example : p ∧ p :=
by tauto

end tauto₀

section tauto₁
variables α : Type
variables p q r : α → Prop
variables h : (∃ x, p x ∧ q x) ∨ (∃ x, p x ∧ r x)
include h
example : ∃ x, p x :=
by tauto

end tauto₁

section tauto₂
variables α : Type
variables x : α
variables p q r : α → Prop
variables h₀ : (∀ x, p x → q x → r x) ∨ r x
variables h₁ : p x
variables h₂ : q x

include h₀ h₁ h₂
example : ∃ x, r x :=
by tauto

end tauto₂

example {x y : ℕ} :
  true :=
begin
  suffices : x = 1 → false, trivial,
  intros a,
  wlog h : x = y,
  { guard_target x = y ∨ y = x,
    admit },
  { guard_hyp h := x = y,
    guard_hyp a := x = 1,
    admit },
end

example {x y : ℕ} :
  true :=
begin
  suffices : false, trivial,
  wlog h : x ≤ y,
  { guard_hyp h := x ≤ y,
    guard_target false,
    admit },
end

example {x y z : ℕ} :
  true :=
begin
  suffices : false, trivial,
  wlog h : x ≤ y + z,
  { guard_target x ≤ y + z ∨ x ≤ z + y,
    admit },
  { guard_hyp h := x ≤ y + z,
    guard_target false,
    admit },
end

example {x y z : ℕ} :
  true :=
begin
  suffices : false, trivial,
  wlog : x ≤ y + z using x y,
  { guard_target x ≤ y + z ∨ y ≤ x + z,
    admit },
  { guard_hyp a := x ≤ y + z,
    guard_target false,
    admit },
end
