/-
Copyright (c) 2021 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Yaël Dillies
-/

import computability.NFA

/-!
# Epsilon Nondeterministic Finite Automata

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition of an epsilon Nondeterministic Finite Automaton (`ε_NFA`), a state
machine which determines whether a string (implemented as a list over an arbitrary alphabet) is in a
regular set by evaluating the string over every possible path, also having access to ε-transitons,
which can be followed without reading a character.
Since this definition allows for automata with infinite states, a `fintype` instance must be
supplied for true `ε_NFA`'s.
-/

open set
open_locale computability

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

variables {α : Type u} {σ σ' : Type v} (M : ε_NFA α σ) {S : set σ} {x : list α} {s : σ} {a : α}

namespace ε_NFA

/-- The `ε_closure` of a set is the set of states which can be reached by taking a finite string of
ε-transitions from an element of the set. -/
inductive ε_closure (S : set σ) : set σ
| base : ∀ s ∈ S, ε_closure s
| step : ∀ s (t ∈ M.step s none), ε_closure s → ε_closure t

@[simp] lemma subset_ε_closure (S : set σ) : S ⊆ M.ε_closure S := ε_closure.base

@[simp] lemma ε_closure_empty : M.ε_closure ∅ = ∅ :=
eq_empty_of_forall_not_mem $ λ s hs, by induction hs with t ht _ _ _ _ ih; assumption

@[simp] lemma ε_closure_univ : M.ε_closure univ = univ :=
eq_univ_of_univ_subset $ subset_ε_closure _ _

/-- `M.step_set S a` is the union of the ε-closure of `M.step s a` for all `s ∈ S`. -/
def step_set (S : set σ) (a : α) : set σ := ⋃ s ∈ S, M.ε_closure $ M.step s a

variables {M}

@[simp] lemma mem_step_set_iff : s ∈ M.step_set S a ↔ ∃ t ∈ S, s ∈ M.ε_closure (M.step t a) :=
mem_Union₂

@[simp] lemma step_set_empty (a : α) : M.step_set ∅ a = ∅ :=
by simp_rw [step_set, Union_false, Union_empty]

variables (M)

/-- `M.eval_from S x` computes all possible paths through `M` with input `x` starting at an element
of `S`. -/
def eval_from (start : set σ) : list α → set σ :=
list.foldl M.step_set (M.ε_closure start)

@[simp] lemma eval_from_nil (S : set σ) : M.eval_from S [] = M.ε_closure S := rfl
@[simp] lemma eval_from_singleton (S : set σ) (a : α) :
  M.eval_from S [a] = M.step_set (M.ε_closure S) a := rfl
@[simp] lemma eval_from_append_singleton (S : set σ) (x : list α) (a : α) :
  M.eval_from S (x ++ [a]) = M.step_set (M.eval_from S x) a :=
by simp only [eval_from, list.foldl_append, list.foldl_cons, list.foldl_nil]

@[simp] lemma eval_from_empty (x : list α) : M.eval_from ∅ x = ∅ :=
begin
  induction x using list.reverse_rec_on with x a ih,
  { rw [eval_from_nil, ε_closure_empty] },
  { rw [eval_from_append_singleton, ih, step_set_empty] }
end

/-- `M.eval x` computes all possible paths through `M` with input `x` starting at an element of
`M.start`. -/
def eval := M.eval_from M.start

@[simp] lemma eval_nil : M.eval [] = M.ε_closure M.start := rfl
@[simp] lemma eval_singleton (a : α) : M.eval [a] = M.step_set (M.ε_closure M.start) a := rfl
@[simp] lemma eval_append_singleton (x : list α) (a : α) :
  M.eval (x ++ [a]) = M.step_set (M.eval x) a :=
eval_from_append_singleton _ _ _ _

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : language α := {x | ∃ S ∈ M.accept, S ∈ M.eval x}

/-! ### Conversions between `ε_NFA` and `NFA` -/

/-- `M.to_NFA` is an `NFA` constructed from an `ε_NFA` `M`. -/
def to_NFA : NFA α σ :=
{ step := λ S a, M.ε_closure (M.step S a),
  start := M.ε_closure M.start,
  accept := M.accept }

@[simp] lemma to_NFA_eval_from_match (start : set σ) :
  M.to_NFA.eval_from (M.ε_closure start) = M.eval_from start := rfl

@[simp] lemma to_NFA_correct :
  M.to_NFA.accepts = M.accepts :=
begin
  ext x,
  rw [accepts, NFA.accepts, eval, NFA.eval, ←to_NFA_eval_from_match],
  refl
end

lemma pumping_lemma [fintype σ] {x : list α} (hx : x ∈ M.accepts)
  (hlen : fintype.card (set σ) ≤ list.length x) :
  ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ fintype.card (set σ) ∧ b ≠ [] ∧
    {a} * {b}∗ * {c} ≤ M.accepts :=
begin
  rw ←to_NFA_correct at hx ⊢,
  exact M.to_NFA.pumping_lemma hx hlen
end

end ε_NFA

namespace NFA

/-- `M.to_ε_NFA` is an `ε_NFA` constructed from an `NFA` `M` by using the same start and accept
  states and transition functions. -/
def to_ε_NFA (M : NFA α σ) : ε_NFA α σ :=
{ step := λ s a, a.cases_on' ∅ (λ a, M.step s a),
  start := M.start,
  accept := M.accept }

@[simp] lemma to_ε_NFA_ε_closure (M : NFA α σ) (S : set σ) : M.to_ε_NFA.ε_closure S = S :=
begin
  ext a,
  refine ⟨_, ε_NFA.ε_closure.base _⟩,
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩),
  { exact h },
  { cases h }
end

@[simp] lemma to_ε_NFA_eval_from_match (M : NFA α σ) (start : set σ) :
  M.to_ε_NFA.eval_from start = M.eval_from start :=
begin
  rw [eval_from, ε_NFA.eval_from, to_ε_NFA_ε_closure],
  congr,
  ext S s,
  simp only [step_set, ε_NFA.step_set, exists_prop, set.mem_Union],
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

/-! ### Regex-like operations -/

namespace ε_NFA

instance : has_zero (ε_NFA α σ) := ⟨⟨λ _ _, ∅, ∅, ∅⟩⟩
instance : has_one (ε_NFA α σ) := ⟨⟨λ _ _, ∅, univ, univ⟩⟩

instance : inhabited (ε_NFA α σ) := ⟨0⟩

variables (P : ε_NFA α σ) (Q : ε_NFA α σ')

@[simp] lemma step_zero (s a) : (0 : ε_NFA α σ).step s a = ∅ := rfl
@[simp] lemma step_one (s a) : (1 : ε_NFA α σ).step s a = ∅ := rfl

@[simp] lemma start_zero : (0 : ε_NFA α σ).start = ∅ := rfl
@[simp] lemma start_one : (1 : ε_NFA α σ).start = univ := rfl

@[simp] lemma accept_zero : (0 : ε_NFA α σ).accept = ∅ := rfl
@[simp] lemma accept_one : (1 : ε_NFA α σ).accept = univ := rfl

end ε_NFA
