/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic data.set

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

example {x : ℕ} (S₀ S₁ : set ℕ)
  (P : ℕ → Prop)
  (h : x ∈ S₀ ∪ S₁) :
  true :=
begin
  suffices : false, trivial,
  wlog h' : x ∈ S₀ using S₀ S₁,
  { guard_hyp h  := x ∈ S₀ ∪ S₁,
    guard_hyp h' := x ∈ S₀,
    admit }
end

example (m n p q : nat) (h : m + n = p) : true :=
begin
  have : m + n = q,
  { generalize_hyp h' : m + n = x at h,
    guard_hyp h' := m + n = x,
    guard_hyp h := x = p,
    guard_target m + n = q,
    admit },
  have : m + n = q,
  { generalize_hyp h' : m + n = x at h ⊢,
    guard_hyp h' := m + n = x,
    guard_hyp h := x = p,
    guard_target x = q,
    admit },
  trivial
end

example (α : Sort*) (L₁ L₂ L₃ : list α)
  (H : L₁ ++ L₂ = L₃) : true :=
begin
  have : L₁ ++ L₂ = L₂,
  { generalize_a h : L₁ ++ L₂ = L at H,
    induction L with hd tl ih,
    case list.nil
    { tactic.cleanup,
      change list.nil = L₃ at H,
      admit },
    case list.cons
    { change hd :: tl = L₃ at H,
      admit } },
  trivial
end

section
open set

variables {α β : Type}
local attribute [simp]
private lemma singleton_inter_singleton_eq_empty {x y : α} :
  ({x} ∩ {y} = (∅ : set α)) ↔ x ≠ y :=
by simp [singleton_inter_eq_empty]

example {f : β → α} {x y : α} (h : x ≠ y) : f ⁻¹' {x} ∩ f ⁻¹' {y} = ∅ :=
begin
  have : {x} ∩ {y} = (∅ : set α) := by simpa using h,
  convert preimage_empty,
  rw [←preimage_inter,this],
end

end

