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

-- Fail if the equivalence can't be used.
example {α β γ : Type} (e : β ≃ γ) (a : α) : α :=
begin
  success_if_fail { equiv_rw e at a },
  success_if_fail { equiv_rw e },
  exact a,
end

-- We can rewrite the goal under functors.
example {α β : Type} (e : α ≃ β) (b : β) : option α :=
begin
  equiv_rw e,
  exact some b,
end

-- We can rewrite hypotheses under functors.
example {α β : Type} (e : α ≃ β) (b : option α) : option β :=
begin
  equiv_rw e at b,
  exact b,
end

-- We can rewrite hypotheses under compositions of functors.
example {α β : Type} (e : α ≃ β) (b : list (list α)) : list β :=
begin
  equiv_rw e at b,
  exact b.join,
end


-- Check that we can rewrite in the target position of function types.
example {α β γ : Type} (e : α ≃ β) (f : γ → β) : γ → α :=
begin
  equiv_rw e,
  exact f,
end

-- Check that we can rewrite in the source position of function types.
example {α β γ : Type} (e : α ≃ β) (f : β → γ) : α → γ :=
begin
  equiv_rw e,
  exact f,
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

-- Rewriting in multiple positions.
example {α β : Type} [has_add β] (e : α ≃ β) : α → α → α :=
begin
  equiv_rw e,
  exact (+),
end

example {α β γ : Type} (e : α ≃ β) (s : β ⊕ γ) : α ⊕ γ :=
begin
  equiv_rw e,
  exact s,
end

example {α β γ : Type} (e : α ≃ β) (s : β ⊕ γ) : (α ⊕ γ) × (γ ⊕ α) :=
begin
  equiv_rw e,
  exact (s, s.swap),
end

example {α β γ : Type} (e : α ≃ β) (s : α ⊕ γ) : (β ⊕ γ) × (γ ⊕ β) :=
begin
  equiv_rw e at s,
  exact (s, s.swap),
end

example {α β γ : Type} (e : α ≃ β) (s : (α ⊕ γ) × β) : (β ⊕ γ) :=
begin
  equiv_rw e at s,
  exact s.1,
end

example {α β : Type} (e : α ≃ β) (P : α → Prop) (h : ∀ a : α, P a) (b : β) : P (e.symm b) :=
begin
  equiv_rw e.symm at b,
  exact h b,
end

example {α β : Type} (e : α ≃ β) (P : α → Sort*) (h : Π a : α, P a) (b : β) : P (e.symm b) :=
begin
  -- this is a bit perverse, as `equiv_rw e.symm at b` is more natural,
  -- but this tests rewriting inside dependent functions
  equiv_rw e at h,
  dsimp at h,
  exact h _,
end
