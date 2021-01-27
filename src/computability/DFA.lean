/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/

import data.fintype.basic
import computability.language
import tactic.norm_num
import tactic.omega.main

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

lemma mem_accepts (x : list α) : x ∈ M.accepts ↔ M.eval_from M.start x ∈ M.accept := by refl

/-- `M.state_path s x` is the states the DFA passes through when evalulating `M.eval_from s x` -/
def state_path : σ → list α → list σ
| start [] := [start]
| start (a :: x) := start :: state_path (M.step start a) x

@[simp] lemma length_state_path (start : σ) (x : list α) :
  (M.state_path start x).length = x.length + 1 :=
begin
  induction x generalizing start,
  refl,
  tauto
end

lemma nth_le_state_path_eq_eval_from_take (start : σ) (x : list α) (n : ℕ)
(h : n < (M.state_path start x).length) :
  (M.state_path start x).nth_le n h = M.eval_from start (x.take n) :=
begin
  induction n with n ih generalizing start x,
  { rw [list.take_zero, eval_from, list.foldl],
    cases x,
    all_goals
    { unfold state_path,
      rw list.nth_le } },
  { cases x,
    { rw [state_path, list.length_singleton, nat.lt_succ_iff, le_zero_iff_eq] at h,
      contradiction },
    unfold state_path,
    rw [list.take, list.nth_le, eval_from, list.foldl],
    apply ih }
end

lemma eval_from_of_append (start : σ) (x y : list α) :
  M.eval_from start (x ++ y) = M.eval_from (M.eval_from start x) y :=
begin
  induction x with a x ih generalizing start,
  { repeat {rw eval_from},
    rw [list.nil_append, list.foldl] },
  { rw [list.cons_append, eval_from, list.foldl],
    apply ih }
end

variable [fintype σ]

lemma pumping_lemma (x : list α) (hx : x ∈ M.accepts) (hlen : (fintype.card σ + 1) ≤ list.length x)
: ∃ a b c,  x = a ++ b ++ c ∧ b ≠ [] ∧ (a ++ b).length ≤ (fintype.card σ + 1) ∧
  {a} * language.star {b} * {c} ≤ M.accepts :=
begin
  -- By pidgeon hole principal the DFA passes though the same state twice in the first p+1 states we
  -- pass through. Let these be the `n`th and `m`th states with `n < m`
  have hnfintype : ∀ n : fin (fintype.card σ + 1), ↑n < (M.state_path M.start x).length,
  { intro n,
    cases n with n h,
    rw [length_state_path, fin.coe_mk],
    apply lt_of_lt_of_le h,
    rw nat.le_add_one_iff,
    left,
    assumption },
  have h := fintype.exists_ne_map_eq_of_card_lt
    (λ n : fin (fintype.card σ + 1), (M.state_path M.start x).nth_le n (hnfintype n)) (by norm_num),
  rcases h with ⟨ n, m, hneq, heq ⟩,
  cases m with m hm, cases n with n hn,
  wlog hle : n ≤ m using [n m, m n],
  { exact le_total n m },
  change list.nth_le _ n _ = list.nth_le _ m _ at heq,
  rw [nth_le_state_path_eq_eval_from_take, nth_le_state_path_eq_eval_from_take] at heq,

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
    rw [min_eq_left_of_lt, nat.sub_eq_zero_iff_le] at hlen,
    { apply hneq,
      apply le_antisymm,
      assumption' },
    apply lt_of_lt_of_le hm,
    assumption },
  split,
  { -- `(a ++ b).length ≤ p` follows easily
    simp only [list.length_take, min_le_iff, list.take_append_drop],
    left,
    apply le_of_lt,
    assumption },

  -- We now show `M` accepts `y := a ++ i*b ++ c` by induction on `i` and showing `a ++ i*b`
  -- always finishes on the same state
  rw [language.star_eq_supr_pow, language.mul_supr, language.supr_mul],
  intros y hy,
  rw set.mem_Union at hy,
  cases hy with i hy,
  rw language.mem_mul at hy,
  rcases hy with ⟨ a, c, ha, hc, hy ⟩,
  have hnstate_path : n < (M.state_path M.start x).length,
  { rw length_state_path,
    apply lt_of_lt_of_le hn,
    rw nat.le_add_one_iff,
    left,
    assumption },
  have h : M.eval_from M.start a = (M.state_path M.start x).nth_le n hnstate_path,
  { induction i with i ih generalizing a y,
    { rw [pow_zero, mul_one, set.mem_singleton_iff] at ha,
      rw [ha, list.take_take, min_eq_left hle, ←nth_le_state_path_eq_eval_from_take] },
    { rw [pow_succ', ←mul_assoc, language.mem_mul] at ha,
      rcases ha with ⟨ a', b, ha', hb, ha ⟩,
      specialize ih a' ha' rfl,
      rw set.mem_singleton_iff at hb,
      rw [←ha, eval_from_of_append, ih, nth_le_state_path_eq_eval_from_take, hb,
          ←eval_from_of_append, ←min_eq_left hle, ←list.take_take, min_eq_left hle,
          list.take_append_drop, list.take_take, min_eq_left hle],
      exact heq.symm } },

  rw set.mem_singleton_iff at hc,
  rw [←hy, mem_accepts, eval_from_of_append, h, nth_le_state_path_eq_eval_from_take, heq,
    ←eval_from_of_append, hc, list.take_append_drop],
  exact hx
end

end DFA
