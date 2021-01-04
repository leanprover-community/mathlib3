/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/

import data.fintype.basic
import computability.language

/-!
# Deterministic Finite Automata
This file contains the definition of a Deterministic Finite Automaton (DFA), a state machine which
determines whether a string (implemented as a list over an arbitrary alphabet) is in a regular set
in linear time.
Note that this definition allows for Automaton with infinite states, a `fintype` instance must be
supplied for true DFA's.
-/

universes u v

/-- A DFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`). -/
structure DFA (α : Type u) (σ : Type v) :=
(step : σ → α → σ)
(start : σ)
(accept : set σ)

namespace DFA

variables {α : Type u} {σ : Type v} (M : DFA α σ)

instance [inhabited σ] : inhabited (DFA α σ) :=
⟨DFA.mk (λ _ _, default σ) (default σ) ∅⟩

/-- `M.eval_from s x` evaluates `M` with input `x` starting from the state `s`. -/
def eval_from (start : σ) : list α → σ :=
list.foldl M.step start

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`. -/
def eval := M.eval_from M.start

/-- `M.accepts` is the language of `x` such that `M.eval x` is an accept state. -/
def accepts : language α :=
λ x, M.eval x ∈ M.accept

end DFA
