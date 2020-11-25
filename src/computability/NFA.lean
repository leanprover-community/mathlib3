/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/

import data.fintype.basic
import computability.DFA

/-!
# Nondeterministic Finite Automata
This file contains the definition of a Nondeterministic Finite Automata (NFA), a state machine which
determines whether a string (implemented as a list over an arbitrary alphabet) is in a regular set
by evaluating  the string over every possible path.
We show that DFA's are equivalent to NFA's however the construction from NFA to DFA uses an
exponential number of states.
-/

universes u v

/-- An NFA is a set of states (`state`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `finset` of states. These are the states that it
  may be sent to. -/
structure NFA (alphabet : Type u) :=
(state : Type v)
[state_fintype : fintype state]
[state_dec : decidable_eq state]
(step : state → alphabet → finset state)
(start : finset state)
(accept : finset state)

namespace NFA

variables {α : Type u} (M : NFA α)

instance NFA_inhabited : inhabited (NFA α) := ⟨ NFA.mk pempty pempty.elim ∅ ∅ ⟩

instance dec := M.state_dec
instance fin := M.state_fintype

/-- `M.step_set S a` is the union of `M.step s a` for all `s ∈ S` -/
def step_set : finset M.state → α → finset M.state :=
λ Ss a, finset.bind Ss (λ S, (M.step S a))

lemma mem_step_set (s : M.state) (S : finset M.state) (a : α) :
  s ∈ M.step_set S a ↔ ∃ t ∈ S, s ∈ M.step t a :=
by rw [step_set, finset.mem_bind]

/-- `M.eval_from S x` computes all possible paths though `M` with input `x` starting at an element
  of `S` -/
def eval_from (start : finset M.state) : list α → finset M.state :=
list.foldl M.step_set start

/-- `M.eval x` computes all possible paths though `M` with input `x` starting at an element of
  `M.start` -/
def eval := M.eval_from M.start

/-- `M.accepts x` says that there is an accept state in `M.eval x` -/
def accepts (s : list α) : Prop :=
∃ S ∈ M.accept, S ∈ M.eval s

/-- Two DFA's are equivalent if the accept exactly the same strings -/
def equiv (M N : NFA α) : Prop := ∀ x, M.accepts x ↔ N.accepts x

local infix ` ≈ ` := equiv

@[refl] lemma equiv_refl (M : NFA α) : M ≈ M := λ x, by refl
@[symm] lemma equiv_symm (M N : NFA α) : M ≈ N → N ≈ M := λ h x, (h x).symm
@[trans] lemma equiv_trans (M N P : NFA α) : M ≈ N → N ≈ P → M ≈ P :=
  λ h₁ h₂ x, iff.trans (h₁ x) (h₂ x)

@[simp] lemma equiv_def (M N : NFA α) : M ≈ N ↔ ∀ x, M.accepts x ↔ N.accepts x :=
  by refl

/-- `NFA_of_DFA M` is an `NFA` constructed from a `DFA` `M` by using the same start and accept
  states and a transition function which sends `s` with input `a` to the singleton `M.step s a` -/
def NFA_of_DFA (M : DFA α) : NFA α :=
{ state := M.state,
  state_fintype := M.state_fintype,
  step := λ s a, {M.step s a},
  start := {M.start},
  accept := M.accept }

lemma NFA_of_DFA_eval_from_match (M : DFA α) (start : M.state) (s : list α) :
  {M.eval_from start s} = (NFA_of_DFA M).eval_from {start} s :=
begin
  change {list.foldl M.step start s} = list.foldl (NFA_of_DFA M).step_set {start} s,
  induction s with a s ih generalizing start,
  { tauto },
  { rw [list.foldl, list.foldl],
    have h : (NFA_of_DFA M).step_set {start} a = {M.step start a},
    { rw step_set,
      finish },
    rw h,
    tauto }
end

lemma NFA_of_DFA_correct (M : DFA α) (x : list α) :
  M.accepts x ↔ (NFA_of_DFA M).accepts x :=
begin
  change _ ↔ ∃ S H, S ∈ (NFA_of_DFA M).eval_from {M.start} x,
  rw ←NFA_of_DFA_eval_from_match,
  split,
  { intro h,
    use M.eval x,
    finish },
  { rintro ⟨ S, hS₁, hS₂ ⟩,
    rw finset.mem_singleton at hS₂,
    rw hS₂ at hS₁,
    assumption }
end

/-- `DFA_of_NFA M` is an `DFA` constructed from a `NFA` `M` using the subset construction. The
  states is the type of `finset`s of `M.state` and the step function is `M.step_set`. -/
def DFA_of_NFA : DFA α :=
{ state := finset M.state,
  step := M.step_set,
  start := M.start,
  accept := finset.univ.filter (λ S, ∃ s ∈ S, s ∈ M.accept) }

lemma DFA_of_NFA_correct (x : list α) :
  M.accepts x ↔ M.DFA_of_NFA.accepts x :=
begin
  rw [accepts, DFA.accepts, eval, DFA.eval],
  change _ ↔ list.foldl _ _ _ ∈ finset.univ.filter _,
  rw finset.mem_filter,
  finish
end

end NFA
