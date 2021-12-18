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
  {a} * language.star {b} * {c} ≤ M.accepts :=
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

namespace ε_NFA

/-!
# Operations on Epsilon Nondeterministic Finite Automata
For any alphabet `α` the class of `ε_NFA`s over `α` is closed under the regular operations

-- * `0` (`zero`) matches nothing
-- * `1` (`ε`) matches only the empty string, ε
-- * `char a` matches only the string 'a'
-- * `P + Q` (`plus P Q`) matches anything which match `P` or `Q`
-- * `P * Q` (`comp P Q`) matches `x ++ y` if `x` matches `P` and `y` matches `Q`
-- * `star P` matches any finite concatenation of strings which match `P`


/-- An `ε_NFA` is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `set` of states and can make ε-transitions by
  inputing `none`.
-/
-- structure ε_NFA (α : Type u) (σ : Type v) :=
-- (step : σ → option α → set σ)
-- (start : set σ)
-- (accept : set σ)

-- Sipser:
-- 1. Q is a finite set of states,  => σ
-- 2. Σ is a finite alphabet,       => α
-- 3. δ: Q x Σ ∪ {ε} → P(Q) is the transition function,  => step
-- 4. q_0 ∈ Q is the start state, and   => start  NB: WE HAVE A **SET** OF START STATES
-- S. F ⊆ Q is the set of accept states. => accept
-/

section closure

variables [decidable_eq α]

def zero_NFA : ε_NFA α (fin 1) := {
  step    := λ s x, {0},
  start   := {0},
  accept  := ∅,
}

def one_NFA : ε_NFA α (fin 1) := {
  step    := λ s x, if (x = none) then {1} else ∅,
  start   := {0},
  accept  := {0},
}

def char_NFA (a : α) : ε_NFA α (fin 2) := {
  step    := λ s x, if (s=0) ∧ (x=a) then {1} else ∅,
  start   := {0},
  accept  := {1},
}

lemma matches_zero_def : (zero_NFA : ε_NFA α _).accepts = 0 :=
begin
  ext b,
  split,
  { intros h, rcases h with ⟨i, hi1, hi2⟩, cases hi1 },
  { intros h, cases h },
  -- rw language.zero_def,
  -- unfold accepts,

  -- ext b,
  -- simp,
  -- tidy?,
  -- suffices : b ∉ { x : list α | ∃ (S : fin 1), S ∈ zero_NFA.accept ∧ S ∈ zero_NFA.eval x},
  -- { exact this },

  -- intros H,
  -- simp at H,
  -- rcases H with ⟨i, hi1, hi2⟩,
  -- exact hi1,
end

lemma matches_one_def  : (one_NFA  : ε_NFA α _).accepts = 1 :=
begin
  ext b, simp,
  split,
  {
    intros h, rcases h with ⟨i, hi1, hi2⟩,
    cases hi1,
    simp at hi1 hi2,
    clear hi1,  -- this is just true by definition, so no longer useful
    unfold eval at hi2,
    unfold eval_from at hi2,
    sorry},
  {
    intros h,
    rw h,
    unfold accepts,
    dsimp at *, simp at *, fsplit, work_on_goal 0 { fsplit, work_on_goal 1 { simp at * } }, fsplit, work_on_goal 0 { ext1, refl }, dsimp at *,
    sorry},
  -- rw language.one_def,
  -- unfold accepts,
end


lemma matches_char_def (a : α) : (char_NFA a : ε_NFA α _).accepts = {[a]} :=
begin

  sorry,
end




end closure
end ε_NFA
