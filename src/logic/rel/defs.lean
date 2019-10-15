/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Yury Kudryashov
-/
import logic.function

universes u v w x

variables (α : Type u) (β : Type v) {γ : Type w} {δ : Type x}

/-- A relation on `α` and `β`, aka a set-valued function, aka a partial multifunction --/
def rel := α → β → Prop

reserve infixr ` ⟹ `:40

variables {α β}

namespace rel

variables (r : rel α β)

/-- The identity relation. -/
protected def id (α) : rel α α := @eq α

/-- Converse relation -/
protected def conv : rel β α := flip r

/-- Composition of relations -/
def comp (r : rel β γ) (s : rel α β) : rel α γ :=
λ x z, ∃ y, r y z ∧ s x y

/-- Restriction of a relation to the diagonal. -/
def diag (r : rel α α) : α → Prop := λ x, r x x

/-- A relation is `left_total`, if its domain is `univ`. -/
def left_total := ∀a, ∃b, r a b
/-- A relation is `right_total`, if its codomain is `univ`. -/
def right_total := ∀b, ∃a, r a b
/-- A relation is `bi_total`, it it is both `left_total` and `right_total`. -/
def bi_total := left_total r ∧ right_total r

/-- A relation is `left_unique`, if each `b` has at most one preimage. -/
def left_unique := ∀⦃a b c⦄, r a c → r b c → a = b
/-- A relation is `right_unique`, if each `a` has at most one image. -/
def right_unique := ∀⦃a b c⦄, r a b → r a c → b = c
/-- A relation is `bi_unique`, if it is both `left_unique` and `right_unique`. -/
def bi_unique : Prop := left_unique r ∧ right_unique r

variable (r)

/-- Graph of a relation -/
protected def graph : set (α × β) := { x : α × β | r x.fst x.snd }

/-- Reconstruct a relation by its graph. -/
def of_graph (s : set (α × β)) : rel α β := function.curry s

/-- Domain of a relation -/
def dom : set α := {x | ∃ y, r x y}

/-- Codomain of a relation. TODO: codomain or range? -/
def codom : set β := {y | ∃ x, r x y}

/-- Image of a set under a relation -/
def image (s : set α) : set β := {y | ∃ x ∈ s, r x y}

/-- Preimage of a set under a relation `r`. Same as the image of `s` under `r.inv` -/
def preimage (s : set β) : set α := r.conv.image s

/-- Core of a set `s : set β` w.r.t `r : rel α β` is the set of `x : α` that are related *only* to elements of `s`. -/
def core (s : set β) := {x | ∀ ⦃y⦄, r x y → y ∈ s}

/-- Restrict the domain of a relation -/
def restrict (s : set α) : rel α β :=
λ x y, x ∈ s ∧ r x y

/-- Lift a pair of relations to a relation on functions. -/
def lift_fun (rac : rel α γ) (rbd : rel β δ) : rel (α → β) (γ → δ) :=
λ f g, ∀⦃x y⦄, rac x y → rbd (f x) (g y)

infixr ⟹ := lift_fun

-- TODO: better name?
def lift_fun_rev (rac : rel α γ) (rbd : rel β δ) : rel (α → β) (γ → δ) :=
λ f g, ∀⦃x y⦄, rbd (f x) (g y) → rac x y

end rel

/-- Graph of a function as a relation. -/
def function.graph' (f : α → β) : rel α β := λ x y, f x = y

def function.graph (f : α → β) : set (α × β) := (function.graph' f).graph
