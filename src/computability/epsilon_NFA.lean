/-
Copyright (c) 2021 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/

import computability.NFA

/-!
# Epsilon Nondeterministic Finite Automata
This file contains the definition of an epsilon Nondeterministic Finite Automaton (ε_NFA), a state
machine which determines whether a string (implemented as a list over an arbitrary alphabet) is in a
regular set by evaluating the string over every possible path, also having access to ε-transitons,
which can be followed without reading a character.
Note that this definition allows for Automaton with infinite states, a `fintype` instance must be
supplied for true ε_NFA's.
-/

universes u v

/-- An ε_NFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `set` of states and can make ε-transitions by
  inputing `none`. -/
structure ε_NFA (α : Type u) (σ : Type v) :=
(step : σ → option α → set σ)
(start : set σ)
(accept : set σ)

variables {α : Type u} {σ σ' : Type v} (M : ε_NFA α σ)

namespace ε_NFA

instance : inhabited (ε_NFA α σ) := ⟨ ε_NFA.mk (λ _ _, ∅) ∅ ∅ ⟩

/-- The derived NFA of an ε_NFA `M` is the NFA on `option σ` with transition function exactly the
  transition function of `M`. Note this does not accept the same language as `M`. -/
def derived_NFA : NFA (option α) σ := ⟨ M.step, M.start, M.accept ⟩

/-- The derived NFA input `x` is the language of `x` with any amount of `none`'s inserted inbetween
  the charactrers and at the start and end. -/
def derived_NFA_input (x : list α) : language (option α) :=
  x.foldl (λ l a, l + {[a]} + (language.star {[none]})) (language.star {[none]})

/-- `M.accepts` is the language of `x` such that the derived NFA accepts some string in the derived
  NFA input of `x`. -/
def accepts : language α :=
  λ x, ∃ y ∈ derived_NFA_input x, y ∈ M.derived_NFA.accepts

end ε_NFA

namespace NFA

/-- `M.to_ε_NFA` is an `ε_NFA` constructed from a `NFA` `M` by using the same start and accept
  states and transition functions. -/
def to_ε_NFA (M : NFA α σ) : ε_NFA α σ :=
{ step := λ s a, a.cases_on' ∅ (λ a, M.step s a),
  start := M.start,
  accept := M.accept }

@[simp] lemma to_ε_NFA_correct (M : NFA α σ) :
  M.to_ε_NFA.accepts = M.accepts :=
begin
  ext x,
  split,
  { rintro ⟨ y, hy₁, hy₂ ⟩,
    induction x,
    { rw [ε_NFA.derived_NFA_input, list.foldl, language.mem_star] at hy₁,
      rcases hy₁ with ⟨ S, hy, hS ⟩,
      cases S with a S,
      -- { finish },
      sorry,
      { have : M.to_ε_NFA.derived_NFA.accepts = 0,
        { induction S with b S ih,
          { simp only [list.join, list.append_nil] at hy,
            specialize hS a _,
            rw set.mem_singleton_iff at hS,
            rw [hy, hS, accepts, eval, eval_from] at hy₂,
            rcases hy₂ with ⟨ s, hs, h ⟩,
            simp only [list.foldl, step_set, exists_prop, set.mem_Union, set.bind_def] at h,
             } } }
          },

        },

end

end NFA
