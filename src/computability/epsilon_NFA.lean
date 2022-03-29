/-
Copyright (c) 2021 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Yaël Dillies
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

section move
variables {α : Type*}

section
variables [complete_lattice α] {ι : Sort*} {κ : ι → Sort*} {f : Π i, κ i → α}

@[simp] lemma infi₂_eq_top : (⨅ i j, f i j) = ⊤ ↔ ∀ i j, f i j = ⊤ := by simp_rw infi_eq_top
@[simp] lemma supr₂_eq_bot : (⨆ i j, f i j) = ⊥ ↔ ∀ i j, f i j = ⊥ := by simp_rw supr_eq_bot

end

namespace set
variables {ι : Sort*} {κ : ι → Sort*} {s : set α}

lemma eq_empty_of_forall_not_mem (h : ∀ x, x ∉ s) : s = ∅ := ext $ λ a, iff_of_false (h _) id

@[simp] lemma Union₂_eq_empty {s : Π i, κ i → set α} : (⋃ i j, s i j) = ∅ ↔ ∀ i j, s i j = ∅ := supr₂_eq_bot

@[simp] lemma Inter₂_eq_univ {s : Π i, κ i → set α} :
  (⋂ i j, s i j) = univ ↔ ∀ i j, s i j = univ :=
infi₂_eq_top

@[simp] lemma Union_pos {p : Prop} {s : p → set α} (h : p) : (⋃ i, s i) = s h := supr_pos h
@[simp] lemma Inter_pos {p : Prop} {s : p → set α} (h : p) : (⋂ i, s i) = s h := infi_pos h
@[simp] lemma Union_neg' {p : Prop} {s : p → set α} (h : ¬ p) : (⋃ i, s i) = ∅ := supr_neg h
@[simp] lemma Inter_neg' {p : Prop} {s : p → set α} (h : ¬ p) : (⋂ i, s i) = univ := infi_neg h

end set

lemma option.mem_some (a : α) : a ∈ some a := option.mem_some_iff.2 rfl
lemma option.mem_coe (a : α) : a ∈ (a : option α) := option.mem_some _

end move

open set

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
  ε-transitions from an element of the set -/
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

/-! ### Regex-like operations -/

instance : has_zero (ε_NFA α σ) := ⟨⟨λ _ _, ∅, ∅, ∅⟩⟩
instance : has_one (ε_NFA α σ) := ⟨⟨λ _ _, ∅, univ, univ⟩⟩

instance : inhabited (ε_NFA α σ) := ⟨0⟩

variables (P : ε_NFA α σ) (Q : ε_NFA α σ')

/-- Addition of `ε_NFA`s. The language of `P.add Q` is the sum of the languages of `P` and `Q`.
-/
def add : ε_NFA α (σ × σ') :=
{ step := λ s a, P.step s.1 a ×ˢ Q.step s.2 a,
  start := P.start ×ˢ Q.start,
  accept := {ab | ab.1 ∈ P.accept ∨ ab.2 ∈ Q.accept} }

/-- Multiplication of `ε_NFA`s. The language of `P.mul Q` is the product of the languages of `P` and
`Q`. -/
def mul : ε_NFA α (σ × σ') :=
{ step := λ s a, P.step s.1 a ×ˢ Q.step s.2 a,
  start := P.start ×ˢ Q.start,
  accept := P.accept ×ˢ Q.accept }

def char [decidable_eq α] (a : α) : ε_NFA α (option unit) :=
{ step := λ s, match s with
    | none := λ b, if a ∈ b then {some ()} else ∅
    | some s := λ _, ∅
    end,
  start := univ,
  accept := univ }

def star [decidable_pred (∈ P.accept)] : ε_NFA α (option σ) :=
{ step := λ s a, match s with
    | none := match a with
      | none := some '' P.start
      | some a := ∅
      end
    | some s :=  match a with
      | none := if s ∈ P.accept then insert none (some '' P.step s none) else some '' P.step s none
      | some a := some '' P.step s a
      end
    end,
  start := {none},
  accept := {none} }

@[simp] lemma step_zero (s a) : (0 : ε_NFA α σ).step s a = ∅ := rfl
@[simp] lemma step_one (s a) : (1 : ε_NFA α σ).step s a = ∅ := rfl
@[simp] lemma step_add (s a) : (P.add Q).step s a = P.step s.1 a ×ˢ Q.step s.2 a := rfl
@[simp] lemma step_mul (s a) : (P.mul Q).step s a = P.step s.1 a ×ˢ Q.step s.2 a := rfl

@[simp] lemma step_char_none_left [decidable_eq α] (a : α) (b : option α) :
  (char a).step none b = if a ∈ b then {some ()} else ∅ := rfl
@[simp] lemma step_char_none_some [decidable_eq α] (a : α) :
  (char a).step none (some a) = {some ()} := if_pos rfl
@[simp] lemma step_char_some [decidable_eq α] (a : α) (b : option α) (s : unit) :
  (char a).step (some s) b = ∅ := rfl
@[simp] lemma step_char_none_right [decidable_eq α] (a : α) :
  ∀ s : option unit, (char a).step s none = ∅
| none := by rw [step_char_none_left, if_neg (option.not_mem_none _)]
| (some s) := rfl

@[simp] lemma step_star_none_none [decidable_pred (∈ P.accept)] :
  P.star.step none none = some '' P.start := rfl
@[simp] lemma step_star_none_some [decidable_pred (∈ P.accept)] (a : α) :
  P.star.step none a = ∅ := rfl
@[simp] lemma step_star_some_none [decidable_pred (∈ P.accept)] (s : σ) :
  P.star.step s none =
    if s ∈ P.accept then insert none (some '' P.step s none) else some '' P.step s none := rfl
lemma step_star_some_none_of_mem [decidable_pred (∈ P.accept)] {s} (h : s ∈ P.accept) :
  P.star.step s none = insert none (some '' P.step s none) := if_pos h
lemma step_star_some_none_of_not_mem [decidable_pred (∈ P.accept)] {s} (h : s ∉ P.accept) :
  P.star.step s none = some '' P.step s none := if_neg h

@[simp] lemma start_zero : (0 : ε_NFA α σ).start = ∅ := rfl
@[simp] lemma start_one : (1 : ε_NFA α σ).start = univ := rfl
@[simp] lemma start_add : (P.add Q).start = P.start ×ˢ Q.start := rfl
@[simp] lemma start_mul : (P.mul Q).start = P.start ×ˢ Q.start := rfl
@[simp] lemma start_char [decidable_eq α] (a : α) : (char a).start = univ := rfl
@[simp] lemma start_star [decidable_pred (∈ P.accept)] : P.star.start = {none} := rfl

@[simp] lemma accept_zero : (0 : ε_NFA α σ).accept = ∅ := rfl
@[simp] lemma accept_one : (1 : ε_NFA α σ).accept = univ := rfl
@[simp] lemma accept_add : (P.add Q).accept = {ab | ab.1 ∈ P.accept ∨ ab.2 ∈ Q.accept} := rfl
@[simp] lemma accept_mul : (P.mul Q).accept = P.accept ×ˢ Q.accept := rfl
@[simp] lemma accept_char [decidable_eq α] (a : α) : (char a).accept = univ := rfl
@[simp] lemma accept_star [decidable_pred (∈ P.accept)] : P.star.accept = {none} := rfl

@[simp] lemma ε_closure_zero (S : set σ) : (0 : ε_NFA α σ).ε_closure S = S :=
begin
  refine (subset_ε_closure _ _).antisymm' _,
  rintro s (⟨t, ht⟩ | ⟨t, u, h⟩),
  { exact ht },
  { exact h.elim }
end

@[simp] lemma ε_closure_one (S : set σ) : (1 : ε_NFA α σ).ε_closure S = S :=
begin
  refine (subset_ε_closure _ _).antisymm' _,
  rintro s (⟨t, ht⟩ | ⟨t, u, h⟩),
  { exact ht },
  { exact h.elim }
end

-- @[simp] lemma ε_closure_add (S) : (P.add Q).ε_closure S = {ab | ab.1 ∈ P.accept ∨ ab.2 ∈ Q.accept} := rfl
-- @[simp] lemma ε_closure_mul (S) : (P.mul Q).ε_closure S = P.accept ×ˢ Q.accept := rfl
-- @[simp] lemma ε_closure_char [decidable_eq α] (S) (a : α) : (char a).ε_closure S = univ :=
-- begin

-- end
-- @[simp] lemma ε_closure_star (S) [decidable_pred (∈ P.accept)] : P.star.ε_closure S = {none} := rfl

@[simp] lemma step_set_zero (S : set σ) (a : α) : (0 : ε_NFA α σ).step_set S a = ∅ :=
by simp_rw [step_set, step_zero, ε_closure_empty, Union_empty]

@[simp] lemma step_set_one (S : set σ) (a : α) : (1 : ε_NFA α σ).step_set S a = ∅ :=
by simp_rw [step_set, step_one, ε_closure_empty, Union_empty]

-- @[simp] lemma step_set_add : (P.add Q).step_set S a = {ab | ab.1 ∈ P.accept ∨ ab.2 ∈ Q.accept} := rfl
-- @[simp] lemma step_set_mul : (P.mul Q).step_set S a = P.accept ×ˢ Q.accept := rfl

lemma step_set_char_of_none_mem [decidable_eq α] {S : set (option unit)} (hS : none ∈ S) (a : α) :
  (char a).step_set S a = {some ()} :=
begin
  unfold step_set,
  simp only [Union_option, step_char_none_left, step_char_some, ε_closure_empty, Union_empty,
    union_empty, if_pos (option.mem_coe _), Union_pos hS],
  refine (subset_ε_closure _ _).antisymm' _,
  rintro s (⟨_, hs⟩ | ⟨t, ht, hs⟩),
  { exact hs },
  { rw  step_char_none_right at hs,
    exact hs.elim }
end

lemma step_set_char_of_none_not_mem [decidable_eq α] {S : set (option unit)} (hS : none ∉ S)
  (a : α) :
  (char a).step_set S a = ∅ :=
begin
  refine Union₂_eq_empty.2 (λ s hs, _),
  cases s,
  { exact (hS hs).elim },
  { simp only [step_char_some, ε_closure_empty] }
end

-- @[simp] lemma step_set_star [decidable_pred (∈ P.accept)] : P.star.step_set S a = {none} := rfl

@[simp] lemma eval_from_zero_cons (S : set σ) (x : list α) (a : α) :
  (0 : ε_NFA α σ).eval_from S (a :: x) = ∅ :=
begin
  induction x using list.reverse_rec_on,
  { rw [eval_from_singleton, step_set_zero] },
  { rw [←list.cons_append, eval_from_append_singleton, step_set_zero] }
end

@[simp] lemma eval_from_one_cons (S : set σ) (x : list α) (a : α) :
  (1 : ε_NFA α σ).eval_from S (a :: x) = ∅ :=
begin
  induction x using list.reverse_rec_on,
  { rw [eval_from_singleton, step_set_one] },
  { rw [←list.cons_append, eval_from_append_singleton, step_set_one] }
end

-- @[simp] lemma eval_from_add : (P.add Q).accept = {ab | ab.1 ∈ P.accept ∨ ab.2 ∈ Q.accept} := rfl
-- @[simp] lemma eval_from_mul : (P.mul Q).accept = P.accept ×ˢ Q.accept := rfl

@[simp] lemma eval_from_char [decidable_eq α] (a : α) : (char a).accept = univ := rfl

-- @[simp] lemma eval_from_star [decidable_pred (∈ P.accept)] : P.star.accept = {none} := rfl

@[simp] lemma eval_zero (x : list α) : (0 : ε_NFA α σ).eval x = ∅ := eval_from_empty _ _

@[simp] lemma eval_one_cons (x : list α) (a : α) : (1 : ε_NFA α σ).eval (a :: x) = ∅ :=
begin
  induction x using list.reverse_rec_on,
  { rw [eval_singleton, step_set_one] },
  { rw [←list.cons_append, eval_append_singleton, step_set_one] }
end

-- @[simp] lemma eval_add : (P.add Q).accept = {ab | ab.1 ∈ P.accept ∨ ab.2 ∈ Q.accept} := rfl
-- @[simp] lemma eval_mul : (P.mul Q).accept = P.accept ×ˢ Q.accept := rfl

-- @[simp] lemma eval_char [decidable_eq α] (a : α) : (char a).accept = univ := rfl

-- @[simp] lemma eval_star [decidable_pred (∈ P.accept)] : P.star.accept = {none} := rfl

@[simp] lemma accepts_zero : (0 : ε_NFA α σ).accepts = 0 :=
eq_empty_of_forall_not_mem $ λ _ ⟨s, h, _⟩, set.not_mem_empty _ h

@[simp] lemma accepts_one [nonempty σ] : (1 : ε_NFA α σ).accepts = 1 :=
begin
  ext,
  rw language.mem_one,
  refine ⟨_, λ h, ⟨classical.arbitrary _, mem_univ _, by simp_rw [h, eval_nil, ε_closure_one]⟩⟩,
  rintro ⟨s, _, hs⟩,
  cases x,
  { refl },
  { rw eval_one_cons at hs,
    exact hs.elim }
end

-- @[simp] lemma accepts_add : (P.add Q).accepts = P.accepts + Q.accepts :=
-- begin
--   ext,
--   rw language.mem_add,
-- end

-- @[simp] lemma accepts_mul : (P.mul Q).accepts = P.accepts * Q.accepts :=
-- begin
--   ext,
--   rw language.mem_mul,
-- end

@[simp] lemma accepts_char [decidable_eq α] : (char a).accepts = {[a]} :=
begin
  ext,
  rw mem_singleton_iff,
  split,
  {
    rintro ⟨( _ | s), h, hs⟩,
    cases x,
    simp at *,
  }
end

@[simp] lemma accepts_star [decidable_pred (∈ P.accept)] : P.star.accepts = P.accepts.star :=
begin
  ext,
  rw language.mem_star,
end

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
  simp only [step_set, ε_NFA.step_set, exists_prop, set.mem_Union, set.bind_def],
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
