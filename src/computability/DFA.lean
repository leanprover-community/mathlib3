/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/

import data.fintype.basic

/-!
# Deterministic Finite Automata
This file contains the definition of a Deterministic Finite Automata (DFA), a state machine which
determines whether a string (implemented as a list over an arbritary alphabet) is in a regular set
in linear time.
-/

universes u v

/-- A DFA is a set of states (`state`), a transition function from state to state labled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`) -/
structure DFA (alphabet : Type u) :=
(state : Type v)
[state_fintype : fintype state]
[state_dec : decidable_eq state]
(step : state → alphabet → state)
(start : state)
(accept : finset state)

namespace DFA

variables {α : Type u} (M : DFA α)

instance DFA_inhabited : inhabited (DFA α) := ⟨ DFA.mk punit (λ _ _, punit.star) punit.star ∅ ⟩

instance dec := M.state_dec
instance fin := M.state_fintype

/-- `M.eval_from s x` evalulates `M` with input `x` starting from the state `s` -/
def eval_from (start : M.state) : list α → M.state :=
list.foldl M.step start

/-- `M.eval x` evalulates `M` with input `x` starting from the state `M.start` -/
def eval := M.eval_from M.start

/-- `M.accepts x` says that `M.eval x` is an accept state -/
def accepts (s : list α) : Prop :=
M.eval s ∈ M.accept

end DFA
