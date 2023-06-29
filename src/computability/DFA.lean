/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/

import data.fintype.card
import computability.language
import tactic.norm_num

/-!
# Deterministic Finite Automata

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition of a Deterministic Finite Automaton (DFA), a state machine which
determines whether a string (implemented as a list over an arbitrary alphabet) is in a regular set
in linear time.
Note that this definition allows for Automaton with infinite states, a `fintype` instance must be
supplied for true DFA's.
-/

open_locale computability

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
⟨DFA.mk (λ _ _, default) default ∅⟩

/-- `M.eval_from s x` evaluates `M` with input `x` starting from the state `s`. -/
def eval_from (start : σ) : list α → σ :=
list.foldl M.step start

@[simp] lemma eval_from_nil (s : σ) : M.eval_from s [] = s := rfl
@[simp] lemma eval_from_singleton (s : σ) (a : α) : M.eval_from s [a] = M.step s a := rfl
@[simp] lemma eval_from_append_singleton (s : σ) (x : list α) (a : α) :
  M.eval_from s (x ++ [a]) = M.step (M.eval_from s x) a :=
by simp only [eval_from, list.foldl_append, list.foldl_cons, list.foldl_nil]

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`. -/
def eval : list α → σ := M.eval_from M.start

@[simp] lemma eval_nil : M.eval [] = M.start := rfl
@[simp] lemma eval_singleton (a : α) : M.eval [a] = M.step M.start a := rfl
@[simp] lemma eval_append_singleton (x : list α) (a : α) :
  M.eval (x ++ [a]) = M.step (M.eval x) a :=
eval_from_append_singleton _ _ _ _

lemma eval_from_of_append (start : σ) (x y : list α) :
  M.eval_from start (x ++ y) = M.eval_from (M.eval_from start x) y :=
x.foldl_append _ _ y

/-- `M.accepts` is the language of `x` such that `M.eval x` is an accept state. -/
def accepts : language α :=
λ x, M.eval x ∈ M.accept

lemma mem_accepts (x : list α) : x ∈ M.accepts ↔ M.eval_from M.start x ∈ M.accept := by refl

lemma eval_from_split [fintype σ] {x : list α} {s t : σ} (hlen : fintype.card σ ≤ x.length)
  (hx : M.eval_from s x = t) :
  ∃ q a b c,
  x = a ++ b ++ c ∧
  a.length + b.length ≤ fintype.card σ ∧
  b ≠ [] ∧
  M.eval_from s a = q ∧
  M.eval_from q b = q ∧
  M.eval_from q c = t :=
begin
  obtain ⟨n, m, hneq, heq⟩ := fintype.exists_ne_map_eq_of_card_lt
    (λ n : fin (fintype.card σ + 1), M.eval_from s (x.take n)) (by norm_num),
  wlog hle : (n : ℕ) ≤ m, { exact this hlen hx _ _ hneq.symm heq.symm (le_of_not_le hle), },
  have hm : (m : ℕ) ≤ fintype.card σ := fin.is_le m,
  dsimp at heq,

  refine ⟨M.eval_from s ((x.take m).take n), (x.take m).take n, (x.take m).drop n, x.drop m,
    _, _, _, by refl, _⟩,

  { rw [list.take_append_drop, list.take_append_drop] },

  { simp only [list.length_drop, list.length_take],
    rw [min_eq_left (hm.trans hlen), min_eq_left hle, add_tsub_cancel_of_le hle],
    exact hm },

  { intro h,
    have hlen' := congr_arg list.length h,
    simp only [list.length_drop, list.length, list.length_take] at hlen',
    rw [min_eq_left, tsub_eq_zero_iff_le] at hlen',
    { apply hneq,
      apply le_antisymm,
      assumption' },
    exact hm.trans hlen, },

  have hq :
    M.eval_from (M.eval_from s ((x.take m).take n)) ((x.take m).drop n) =
      M.eval_from s ((x.take m).take n),
  { rw [list.take_take, min_eq_left hle, ←eval_from_of_append, heq, ←min_eq_left hle,
        ←list.take_take, min_eq_left hle, list.take_append_drop] },

  use hq,
  rwa [←hq, ←eval_from_of_append, ←eval_from_of_append, ←list.append_assoc, list.take_append_drop,
       list.take_append_drop]
end

lemma eval_from_of_pow {x y : list α} {s : σ} (hx : M.eval_from s x = s)
  (hy : y ∈ ({x} : language α)∗) : M.eval_from s y = s :=
begin
  rw language.mem_kstar at hy,
  rcases hy with ⟨ S, rfl, hS ⟩,
  induction S with a S ih,
  { refl },
  { have ha := hS a (list.mem_cons_self _ _),
    rw set.mem_singleton_iff at ha,
    rw [list.join, eval_from_of_append, ha, hx],
    apply ih,
    intros z hz,
    exact hS z (list.mem_cons_of_mem a hz) }
end

lemma pumping_lemma [fintype σ] {x : list α} (hx : x ∈ M.accepts)
  (hlen : fintype.card σ ≤ list.length x) :
  ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ fintype.card σ ∧ b ≠ [] ∧
    {a} * {b}∗ * {c} ≤ M.accepts :=
begin
  obtain ⟨_, a, b, c, hx, hlen, hnil, rfl, hb, hc⟩ := M.eval_from_split hlen rfl,
  use [a, b, c, hx, hlen, hnil],
  intros y hy,
  rw language.mem_mul at hy,
  rcases hy with ⟨ ab, c', hab, hc', rfl ⟩,
  rw language.mem_mul at hab,
  rcases hab with ⟨ a', b', ha', hb', rfl ⟩,
  rw set.mem_singleton_iff at ha' hc',
  substs ha' hc',
  have h := M.eval_from_of_pow hb hb',
  rwa [mem_accepts, eval_from_of_append, eval_from_of_append, h, hc]
end

end DFA
