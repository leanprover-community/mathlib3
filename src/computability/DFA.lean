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

instance : setoid (Σ σ, DFA α σ) :=
⟨ λ M N, ∀ x, M.2.accepts x ↔ N.2.accepts x,
  λ _ _, by refl, λ _ _ h x, (h x).symm, λ _ _ _ h₁ h₂ x, iff.trans (h₁ x) (h₂ x) ⟩

instance : has_coe (DFA α σ) (Σ σ, DFA α σ) := ⟨λ M, ⟨σ, M⟩⟩

@[simp] lemma equiv_def (M : DFA α σ₁) (N : DFA α σ₂) :
  (⟨σ₁, M⟩ : (Σ σ, DFA α σ)) ≈ N ↔ ∀ x, M.accepts x ↔ N.accepts x :=
by refl

end DFA
