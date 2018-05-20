/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic data.set.lattice

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

section wlog

example {x y : ℕ} (a : x = 1) : true :=
begin
  suffices : false, trivial,
  wlog h : x = y,
  { guard_target x = y ∨ y = x,
    admit },
  { guard_hyp h := x = y,
    guard_hyp a := x = 1,
    admit }
end

example {x y : ℕ} : true :=
begin
  suffices : false, trivial,
  wlog h : x ≤ y,
  { guard_hyp h := x ≤ y,
    guard_target false,
    admit }
end

example {x y z : ℕ} : true :=
begin
  suffices : false, trivial,
  wlog h : x ≤ y + z,
  { guard_target x ≤ y + z ∨ x ≤ z + y,
    admit },
  { guard_hyp h := x ≤ y + z,
    guard_target false,
    admit }
end

example {x y z : ℕ} : true :=
begin
  suffices : false, trivial,
  wlog : x ≤ y + z using x y,
  { guard_target x ≤ y + z ∨ y ≤ x + z,
    admit },
  { guard_hyp case := x ≤ y + z,
    guard_target false,
    admit },
end

example {x : ℕ} (S₀ S₁ : set ℕ) (P : ℕ → Prop)
  (h : x ∈ S₀ ∪ S₁) : true :=
begin
  suffices : false, trivial,
  wlog h' : x ∈ S₀ using S₀ S₁,
  { guard_target x ∈ S₀ ∨ x ∈ S₁,
    admit },
  { guard_hyp h  := x ∈ S₀ ∪ S₁,
    guard_hyp h' := x ∈ S₀,
    admit }
end

example {n m i : ℕ} {p : ℕ → ℕ → ℕ → Prop} : true :=
begin
  suffices : false, trivial,
  wlog : p n m i using [n m i, n i m, i n m],
  { guard_target p n m i ∨ p n i m ∨ p i n m,
    admit },
  { guard_hyp case := p n m i,
    admit }
end

example {n m i : ℕ} {p : ℕ → Prop} : true :=
begin
  suffices : false, trivial,
  wlog : p n using [n m i, m n i, i n m],
  { guard_target p n ∨ p m ∨ p i,
    admit },
  { guard_hyp case := p n,
    admit }
end

example {n m i : ℕ} {p : ℕ → ℕ → Prop} {q : ℕ → ℕ → ℕ → Prop} : true :=
begin
  suffices : q n m i, trivial,
  have h : p n i ∨ p i m ∨ p m i, from sorry,
  wlog : p n i := h using n m i,
  { guard_hyp h := p n i,
    guard_target q n m i,
    admit },
  { guard_hyp h := p i m,
    guard_hyp this := q i m n,
    guard_target q n m i,
    admit },
  { guard_hyp h := p m i,
    guard_hyp this := q m i n,
    guard_target q n m i,
    admit },
end

end wlog

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
  { generalize_hyp h : L₁ ++ L₂ = L at H,
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

section convert
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

end convert

section rcases

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

example (x : inhabited α × option β ⊕ γ) : true :=
begin
  rcases x with ⟨⟨a⟩, _ | b⟩ | c,
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

end rcases
