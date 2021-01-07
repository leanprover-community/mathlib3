/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/

import data.fintype.basic
import computability.language
import tactic.norm_num

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

variables {α : Type u} {σ σ₁ σ₂ σ₃ : Type v} (M : DFA α σ)

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

def state_path : σ → list α → list σ
| start [] := [start]
| start (a :: x) := M.step start a :: state_path (M.step start a) x

@[simp] lemma length_state_path (start : σ) (x : list α) :
  (M.state_path start x).length = x.length + 1 :=
begin
  induction x generalizing start,
  refl,
  tauto
end

variable [fintype σ]

lemma pumping_lemma : ∃ p : ℕ, ∀ x ∈ M.accepts, p ≤ list.length x → ∃ a b c, x = a ++ b ++ c ∧
  b ≠ [] ∧ (a ++ b).length ≤ p ∧ ∀ n, a ++ (list.repeat b n).foldl (++) [] ++ c ∈ M.accepts :=
begin
  -- Let p be the number of states in our DFA
  use fintype.card σ,
  intros x hMx hlen,

  -- By pidgeon hole principal the DFA passes though the same state twice in the first p+1 states we
  -- pass through. Let these be the `n`th and `m`th states with `n < m`
  let state_map : fin (fintype.card σ + 1) → σ := λ n, (M.state_path M.start x).nth_le n begin cases n with n h, rw [length_state_path, fin.coe_mk], apply lt_of_lt_of_le, assumption, finish end,
  have h := fintype.exists_ne_map_eq_of_card_lt state_map (by norm_num),
  rcases h with ⟨ n, m, hneq, heq ⟩,
  wlog hle : n ≤ m using [n m, m n],
  { exact le_total n m },

  -- Now let `a` be the first `n` characters of `x`, `b` be the next `m-n` characters and `c` the
  -- rest
  use [(x.take m).take n, (x.take m).drop n, x.drop m],
  split,
  { rw [list.take_append_drop, list.take_append_drop] },

  split,
  { -- We shall show that `b` is not nil by showing it's length is not zero
    intro h,
    have hlen := congr_arg list.length h,
    simp only [list.length_drop, list.length, list.length_take] at hlen,
    rw [min_eq_left_of_lt, nat.sub_eq_zero_iff_le, fin.coe_fin_le] at hlen,
    { apply hneq,
      finish },
    cases m with m hb,
    simp,
    apply lt_of_lt_of_le hb,
    assumption,
  },
  {}
end

end DFA
