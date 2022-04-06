/-
Copyright (c) 2021 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/

import computability.NFA

/-!
# Epsilon Nondeterministic Finite Automata
This file contains the definition of an epsilon Nondeterministic Finite Automaton (`ε_NFA`), a state
machine which determines whether a string (implemented as a list over an arbitrary alphabet) is in a
regular set by evaluating the string over every possible path, also having access to ε-transitons,
which can be followed without reading a character.
Since this definition allows for automata with infinite states, a `fintype` instance must be
supplied for true `ε_NFA`'s.
-/

universes u v

/-- An `ε_NFA` is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `set` of states and can make ε-transitions by
  inputing `none`.
  Since this definition allows for Automata with infinite states, a `fintype` instance must be
  supplied for true `ε_NFA`'s.-/
structure ε_NFA (α : Type u) (σ : Type v) :=
(step : σ → option α → set σ)
(start : set σ)
(accept : set σ)

variables {α : Type u} {σ σ' : Type v} (M : ε_NFA α σ)

namespace ε_NFA

instance : inhabited (ε_NFA α σ) := ⟨ ε_NFA.mk (λ _ _, ∅) ∅ ∅ ⟩

/-- The `ε_closure` of a set is the set of states which can be reached by taking a finite string of
  ε-transitions from an element of the set -/
inductive ε_closure : set σ → set σ
| base : ∀ S (s ∈ S), ε_closure S s
| step : ∀ S s (t ∈ M.step s none), ε_closure S s → ε_closure S t

/-- `M.step_set S a` is the union of the ε-closure of `M.step s a` for all `s ∈ S`. -/
def step_set : set σ → α → set σ :=
λ S a, S >>= (λ s, M.ε_closure (M.step s a))

/-- `M.eval_from S x` computes all possible paths though `M` with input `x` starting at an element
  of `S`. -/
def eval_from (start : set σ) : list α → set σ :=
list.foldl M.step_set (M.ε_closure start)

/-- `M.eval x` computes all possible paths though `M` with input `x` starting at an element of
  `M.start`. -/
def eval := M.eval_from M.start

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : language α :=
λ x, ∃ S ∈ M.accept, S ∈ M.eval x

/-- `M.to_NFA` is an `NFA` constructed from an `ε_NFA` `M`. -/
def to_NFA : NFA α σ :=
{ step := λ S a, M.ε_closure (M.step S a),
  start := M.ε_closure M.start,
  accept := M.accept }

@[simp] lemma to_NFA_eval_from_match (start : set σ) :
{ step := λ _ _, ∅,
  accept := ∅ }

lemma pumping_lemma [fintype σ] {x : list α} (hx : x ∈ M.accepts)
  (hlen : fintype.card (set σ) ≤ list.length x) :
  ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ fintype.card (set σ) ∧ b ≠ [] ∧
  {a} * language.star {b} * {c} ≤ M.accepts :=
begin
  rw ←to_NFA_correct at hx ⊢,
  exact M.to_NFA.pumping_lemma hx hlen
end

def epsilon : ε_NFA α punit :=
{ step := λ _ _, ∅,
  start := {punit.star},

def char (a₁ : α) [decidable_eq α] : ε_NFA α (ulift bool) :=
{ step := λ b a₂, if some a₁ = a₂ then (if ↑(ulift.down b) then {⟨ff⟩} else ∅) else ∅,
  start := {⟨tt⟩},
  accept := {⟨ff⟩} }

def plus (M : ε_NFA α σ) (N : ε_NFA α σ') : ε_NFA α (σ × σ') :=
{ step := λ ⟨ s, t ⟩ a, (M.step s a).prod (N.step t a),
  start := M.start.prod N.start,
  accept := M.accept.prod N.accept }

def prod (M : ε_NFA α σ) (N : ε_NFA α σ') [decidable_pred M.accept] : ε_NFA α (σ ⊕ σ') :=
{ step := λ s a, s.elim
    ( λ s,
      if s ∈ M.accept ∧ a.is_none
      then ((sum.inl '' (M.step s a)) ∪ (sum.inr '' N.start))
      else (sum.inl '' (M.step s a)))
    (λ t, (sum.inr '' (N.step t a))),
  start := sum.inl '' M.start,
  accept := sum.inr '' N.accept }

def star (M : ε_NFA α σ) [decidable_pred M.accept] : ε_NFA α σ :=
{ step := λ s a,
    if s ∈ M.accept ∧ a.is_none
    then M.step s a ∪ M.start
    else M.step s a,
  start := M.start,
  accept := M.accept }

lemma zero_accepts : (@zero α).accepts = 0 := by tidy

lemma epsilon_accepts : (@epsilon α).accepts = 1 :=
begin
  ext x,
  rw [language.mem_one, mem_accepts],
  split,
  { rintro ⟨ S, hs, h ⟩, }
end

lemma char_accepts (a : α) [decidable_eq α] : (char a).accepts = {[a]} := by tidy

end ε_NFA

namespace NFA

/-- `M.to_ε_NFA` is an `ε_NFA` constructed from a `NFA` `M` by using the same start and accept
  states and transition functions. -/
def to_ε_NFA (M : NFA α σ) : ε_NFA α σ :=
{ step := λ s a, a.cases_on' ∅ (λ a, M.step s a),
  start := M.start,
  accept := M.accept }

@[simp] lemma to_ε_NFA_ε_closure (M : NFA α σ) (S : set σ) : M.to_ε_NFA.ε_closure S = S :=
begin
  ext a,
  split,
  { rintro ( ⟨ _, _, h ⟩ | ⟨ _, _, _, h, _ ⟩ ),
    exact h,
    cases h },
  { intro h,
    apply ε_NFA.ε_closure.base,
    exact h }
end

@[simp] lemma to_ε_NFA_eval_from_match (M : NFA α σ) (start : set σ) :
  M.to_ε_NFA.eval_from start = M.eval_from start :=
begin
  rw [eval_from, ε_NFA.eval_from, step_set, ε_NFA.step_set, to_ε_NFA_ε_closure],
  congr,
  ext S s,
  simp only [exists_prop, set.mem_Union, set.bind_def],
  apply exists_congr,
  simp only [and.congr_right_iff],
  intros t ht,
  rw M.to_ε_NFA_ε_closure,
  refl
end

@[simp] lemma to_ε_NFA_correct (M : NFA α σ) :
  M.to_ε_NFA.accepts = M.accepts :=
begin
  rw [accepts, ε_NFA.accepts, eval, ε_NFA.eval, to_ε_NFA_eval_from_match],
  refl
end

end NFA
