/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/

import data.fintype.basic

/-!
# Deterministic Finite Automata
This file contains the definition of a Deterministic Finite Automaton (DFA), a state machine which
determines whether a string (implemented as a list over an arbitrary alphabet) is in a regular set
in linear time.
-/

universes u v

/-- A DFA is a set of states (`state`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`). -/
structure DFA (alphabet : Type u) (state : Type v) :=
(step : state → alphabet → state)
(start : state)
(accept : finset state)

namespace DFA

variables {α : Type u} {σ σ₁ σ₂ σ₃ : Type v} (M : DFA α σ)

instance DFA_inhabited [inhabited σ] : inhabited (DFA α σ) :=
⟨DFA.mk (λ _ _, default σ) (default σ) ∅⟩

/-- `M.eval_from s x` evaluates `M` with input `x` starting from the state `s`. -/
def eval_from (start : σ) : list α → σ :=
list.foldl M.step start

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`. -/
def eval := M.eval_from M.start

/-- `M.accepts x` says that `M.eval x` is an accept state. -/
def accepts (x : list α) : Prop :=
M.eval x ∈ M.accept

/-- Two DFA's are equivalent if they accept exactly the same strings. -/
def equiv (M : DFA α σ₁) (N : DFA α σ₂) : Prop := ∀ x, M.accepts x ↔ N.accepts x

local infix ` ≈ ` := equiv

@[refl] lemma equiv_refl (M : DFA α σ) : M ≈ M := λ x, by refl
@[symm] lemma equiv_symm (M : DFA α σ₁) (N : DFA α σ₂) : M ≈ N → N ≈ M := λ h x, (h x).symm
@[trans] lemma equiv_trans (M : DFA α σ₁) (N : DFA α σ₂) (P : DFA α σ₃) : M ≈ N → N ≈ P → M ≈ P :=
  λ h₁ h₂ x, iff.trans (h₁ x) (h₂ x)

instance : setoid (Σ σ, DFA α σ) :=
⟨ λ M N, M.2 ≈ N.2,
  λ M, M.2.equiv_refl, λ M N, M.2.equiv_symm N.2, λ M N P, M.2.equiv_trans N.2 P.2 ⟩

instance : has_coe (DFA α σ) (Σ σ, DFA α σ) := ⟨λ M, ⟨σ, M⟩⟩

@[simp] lemma equiv_def (M : DFA α σ₁) (N : DFA α σ₂) :
  M ≈ N ↔ ∀ x, M.accepts x ↔ N.accepts x :=
by refl

end DFA
