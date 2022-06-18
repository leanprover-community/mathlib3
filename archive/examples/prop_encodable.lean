/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/

import data.W.basic

/-!
# W types

The file `data/W.lean` shows that if `α` is an an encodable fintype and for every `a : α`,
`β a` is encodable, then `W β` is encodable.

As an example of how this can be used, we show that the type of propositional formulas with
variables labeled from an encodable type is encodable.

The strategy is to define a type of labels corresponding to the constructors.
From the definition (using `sum`, `unit`, and an encodable type), Lean can infer
that it is encodable. We then define a map from propositional formulas to the
corresponding `Wfin` type, and show that map has a left inverse.

We mark the auxiliary constructions `private`, since their only purpose is to
show encodability.
-/

/-- Propositional formulas with labels from `α`. -/
inductive prop_form (α : Type*)
| var : α → prop_form
| not : prop_form → prop_form
| and : prop_form → prop_form → prop_form
| or  : prop_form → prop_form → prop_form

/-!
The next three functions make it easier to construct functions from a small
`fin`.
-/

section
variable {α : Type*}

/-- the trivial function out of `fin 0`. -/
def mk_fn0 : fin 0 → α
| ⟨_, h⟩ := absurd h dec_trivial

/-- defines a function out of `fin 1` -/
def mk_fn1 (t : α) : fin 1 → α
| ⟨0, _⟩   := t
| ⟨n+1, h⟩ := absurd h dec_trivial

/-- defines a function out of `fin 2` -/
def mk_fn2 (s t : α) : fin 2 → α
| ⟨0, _⟩   := s
| ⟨1, _⟩   := t
| ⟨n+2, h⟩ := absurd h dec_trivial

attribute [simp] mk_fn0 mk_fn1 mk_fn2
end

namespace prop_form

private def constructors (α : Type*) := α ⊕ unit ⊕ unit ⊕ unit

local notation `cvar` a := sum.inl a
local notation `cnot`   := sum.inr (sum.inl unit.star)
local notation `cand`   := sum.inr (sum.inr (sum.inr unit.star))
local notation `cor`    := sum.inr (sum.inr (sum.inl unit.star))

@[simp]
private def arity (α : Type*) : constructors α → nat
| (cvar a) := 0
| cnot     := 1
| cand     := 2
| cor      := 2

variable {α : Type*}

private def f : prop_form α → W_type (λ i, fin (arity α i))
| (var a)   := ⟨cvar a, mk_fn0⟩
| (not p)   := ⟨cnot, mk_fn1 (f p)⟩
| (and p q) := ⟨cand, mk_fn2 (f p) (f q)⟩
| (or  p q) := ⟨cor, mk_fn2 (f p) (f q)⟩

private def finv : W_type (λ i, fin (arity α i)) → prop_form α
| ⟨cvar a, fn⟩ := var a
| ⟨cnot, fn⟩   := not (finv (fn ⟨0, dec_trivial⟩))
| ⟨cand, fn⟩   := and (finv (fn ⟨0, dec_trivial⟩)) (finv (fn ⟨1, dec_trivial⟩))
| ⟨cor, fn⟩    := or  (finv (fn ⟨0, dec_trivial⟩)) (finv (fn ⟨1, dec_trivial⟩))

instance [encodable α] : encodable (prop_form α) :=
begin
  haveI : encodable (constructors α),
  { unfold constructors, apply_instance },
  exact encodable.of_left_inverse f finv
    (by { intro p, induction p; simp [f, finv, *] })
end

end prop_form
