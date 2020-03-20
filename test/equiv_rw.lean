/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.equiv_rw

-- Rewriting a hypothesis along an equivalence.
example {α β : Type} (e : α ≃ β)
  (f : α → ℕ) (h : ∀ b : β, f (e.symm b) = 0) (i : α) : f i = 0 :=
begin
  equiv_rw e at i,
  apply h,
end

-- Check that dependent hypotheses are reverted and reintroduced.
example {α β : Type} (e : α ≃ β) (Z : α → Type) (f : Π a, Z a → ℕ)
  (h : ∀ (b : β) (x : Z (e.symm b)), f (e.symm b) x = 0)
  (i : α) (x : Z i) : f i x = 0 :=
begin
  equiv_rw e at i,
  guard_hyp i := β,
  guard_target f (e.symm i) x = 0,
  guard_hyp x := Z ((e.symm) i),
  exact h i x,
end

-- Rewriting the goal along an equivalence.
example {α β : Type} (e : α ≃ β) (b : β) : α :=
begin
  equiv_rw e,
  exact b,
end

-- We can rewrite the goal under functors.
example {α β : Type} (e : α ≃ β) (b : β) : option α :=
begin
  equiv_rw e,
  exact some b,
end

-- Check that we can rewrite in the target position of function types.
example {α β γ : Type} (e : α ≃ β) (b : γ → β) : γ → α :=
begin
  equiv_rw e,
  exact b,
end

-- Rewriting under multiple functors.
example {α β : Type} (e : α ≃ β) (b : β) : list (option α) :=
begin
  equiv_rw e,
  exact [none, some b],
end

-- Rewriting under multiple functors, including functions.
example {α β γ : Type} (e : α ≃ β) (b : β) : γ → list (option α) :=
begin
  equiv_rw e,
  exact (λ g, [none, some b]),
end
